import Langlands.MathlibBase
import Langlands.CommutativeAlgebra.FiniteTypeIntGRing.JacobianQuotient
import Langlands.CommutativeAlgebra.Popescu.RegularSequenceFlatStatement
import Langlands.CommutativeAlgebra.Popescu.RegularLocalParametersStatement
import Langlands.CommutativeAlgebra.Popescu.GeometricRegularityFlatCore

/-! # Auxiliary lemmas for the proof of Stacks 07E6 -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace GeometricRegularity

open IsLocalRing

open scoped TensorProduct

/-- A linear map is injective if it maps a finite spanning family to a linearly independent
family. -/
theorem injective_of_span_of_linearIndependent {K M N : Type*} [CommRing K] [AddCommGroup M]
    [Module K M] [AddCommGroup N] [Module K N] {ι : Type*} [Fintype ι] (f : M →ₗ[K] N)
    (u : ι → M) (hspan : Submodule.span K (Set.range u) = ⊤)
    (hli : LinearIndependent K fun i => f (u i)) : Function.Injective f := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro m hm
  have hm' : m ∈ Submodule.span K (Set.range u) := hspan ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hm'
  rw [LinearMap.mem_ker, map_sum] at hm
  simp only [map_smul] at hm
  have := Fintype.linearIndependent_iff.mp hli c hm
  simp [this]

/-- If `u` spans the `A`-module `M`, then the `1 ⊗ u i` span `K ⊗_A M` over `K`. -/
theorem span_one_tmul {A K M : Type*} [CommRing A] [CommRing K] [Algebra A K] [AddCommGroup M]
    [Module A M] {ι : Type*} [Fintype ι] (u : ι → M)
    (hu : Submodule.span A (Set.range u) = ⊤) :
    Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[A] u i) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.inductionOn with
  | tmul c m =>
    have hm : m ∈ Submodule.span A (Set.range u) := hu ▸ Submodule.mem_top
    obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hm
    rw [TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : c ⊗ₜ[A] (b i • u i) = (b i • c) • ((1 : K) ⊗ₜ[A] u i) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | add y z hy hz => exact add_mem hy hz

/-- A Noetherian local ring has a generating family of its maximal ideal indexed by
`Fin (spanFinrank 𝔪)`. -/
theorem exists_fin_span_eq_maximalIdeal (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    ∃ x : Fin (maximalIdeal R).spanFinrank → R, Ideal.span (Set.range x) = maximalIdeal R := by
  obtain ⟨s, hs, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal R))
  refine ⟨fun i => (s.equivFin.symm (Fin.cast hs.symm i) : R), Eq.trans ?_ hspan⟩
  show Submodule.span R _ = Submodule.span R _
  congr 1
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    exact Finset.mem_coe.mpr (s.equivFin.symm _).2
  · intro hy
    exact ⟨Fin.cast hs (s.equivFin ⟨y, Finset.mem_coe.mp hy⟩), by simp⟩

/-- Elements of the maximal ideal of a regular local ring whose classes in `𝔪/𝔪²` are linearly
independent form a weakly regular sequence (they extend to a regular system of parameters, which
is a regular sequence by Stacks 00NQ). -/
theorem isWeaklyRegular_of_linearIndependent (h00NQ : RegularLocalParametersStatement.{u})
    {A : Type u} [CommRing A] [IsRegularLocalRing A] {d : ℕ} (f : Fin d → A)
    (hfm : ∀ i, f i ∈ maximalIdeal A)
    (hf : LinearIndependent (ResidueField A)
      fun i => (maximalIdeal A).toCotangent ⟨f i, hfm i⟩) :
    RingTheory.Sequence.IsWeaklyRegular A (List.ofFn f) := by
  classical
  set κ := ResidueField A
  set V := CotangentSpace A
  set v : Fin d → V := fun i => (maximalIdeal A).toCotangent ⟨f i, hfm i⟩ with hv
  set W : Submodule κ V := Submodule.span κ (Set.range v) with hWdef
  have hW : Module.finrank κ W = d := by
    rw [hWdef, finrank_span_eq_card hf, Fintype.card_fin]
  have hWV := Submodule.finrank_quotient_add_finrank W
  set e := Module.finrank κ (V ⧸ W) with he
  let bq := Module.finBasis κ (V ⧸ W)
  have hsurj : Function.Surjective
      (fun t : maximalIdeal A => W.mkQ ((maximalIdeal A).toCotangent t)) := by
    intro y
    obtain ⟨x, rfl⟩ := W.mkQ_surjective y
    obtain ⟨t, rfl⟩ := (maximalIdeal A).toCotangent_surjective x
    exact ⟨t, rfl⟩
  choose t ht using fun j : Fin e => hsurj (bq j)
  -- the images of the `f i` and the `t j` span the cotangent space
  have hspanV : Submodule.span κ ((maximalIdeal A).toCotangent ''
      (Set.range (fun i => (⟨f i, hfm i⟩ : maximalIdeal A)) ∪ Set.range t)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    set U := Submodule.span κ ((maximalIdeal A).toCotangent ''
      (Set.range (fun i => (⟨f i, hfm i⟩ : maximalIdeal A)) ∪ Set.range t))
    have hWU : W ≤ U := by
      rw [hWdef, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨_, Or.inl ⟨i, rfl⟩, rfl⟩
    have htU : ∀ j, (maximalIdeal A).toCotangent (t j) ∈ U := fun j =>
      Submodule.subset_span ⟨_, Or.inr ⟨j, rfl⟩, rfl⟩
    have hx := bq.sum_repr (W.mkQ x)
    set y : V := ∑ j, bq.repr (W.mkQ x) j • (maximalIdeal A).toCotangent (t j)
    have hy : W.mkQ y = W.mkQ x := by
      rw [← hx, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul]
      congr 1
      exact ht j
    have hxy : x - y ∈ W := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      simpa [sub_eq_zero] using hy.symm
    have hyU : y ∈ U := Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (htU j)
    have := U.add_mem (hWU hxy) hyU
    simpa using this
  have hspanR := (CotangentSpace.span_image_eq_top_iff (R := A)).mp hspanV
  have hmax : maximalIdeal A = Ideal.span (Set.range f ∪ Set.range (fun j => (t j : A))) := by
    have := congrArg (Submodule.map (maximalIdeal A).subtype) hspanR
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span] at this
    refine this.symm.trans ?_
    rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]
    rfl
  -- counting
  have hN : d + e = (maximalIdeal A).spanFinrank := by
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, ← hWV, hW]
    omega
  let g : Fin (d + e) → A := Fin.append f (fun j => (t j : A))
  have hrange : Set.range g = Set.range f ∪ Set.range (fun j => (t j : A)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left j => exact Or.inl ⟨j, (Fin.append_left f (fun j => (t j : A)) j).symm⟩
      | right j => exact Or.inr ⟨j, (Fin.append_right f (fun j => (t j : A)) j).symm⟩
    · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨Fin.castAdd _ j, Fin.append_left f (fun j => (t j : A)) j⟩
      · exact ⟨Fin.natAdd _ j, Fin.append_right f (fun j => (t j : A)) j⟩
  let x : Fin (maximalIdeal A).spanFinrank → A := fun i => g (Fin.cast hN.symm i)
  have hx : Ideal.span (Set.range x) = maximalIdeal A := by
    refine Eq.trans ?_ (hrange ▸ hmax).symm
    congr 1
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨Fin.cast hN j, by simp [x]⟩
  have hreg := (h00NQ A x hx).toIsWeaklyRegular
  have hof : List.ofFn x = List.ofFn f ++ List.ofFn (fun j => (t j : A)) :=
    (List.ofFn_congr hN g).symm.trans (List.ofFn_fin_append _ _)
  rw [hof] at hreg
  exact ((RingTheory.Sequence.isWeaklyRegular_append_iff A _ _).mp hreg).1

/-- The differentials of the variables span `Ω` of a localization of a polynomial ring. -/
theorem span_D_localization (k : Type u) [Field k] (m : ℕ)
    (𝔭 : Ideal (MvPolynomial (Fin m) k)) [𝔭.IsPrime] :
    Submodule.span (Localization.AtPrime 𝔭) (Set.range fun i =>
      KaehlerDifferential.D k (Localization.AtPrime 𝔭)
        (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) (MvPolynomial.X i))) =
      ⊤ := by
  have : Algebra.FormallyEtale (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) :=
    Algebra.FormallyEtale.of_isLocalization 𝔭.primeCompl
  have hb : ∀ i, KaehlerDifferential.mvPolynomialBasis k (Fin m) i =
      KaehlerDifferential.D k (MvPolynomial (Fin m) k) (MvPolynomial.X i) := fun i =>
    Module.Basis.apply_eq_iff.mpr (KaehlerDifferential.mvPolynomialBasis_repr_D_X k (Fin m) i)
  have hspanR : Submodule.span (MvPolynomial (Fin m) k) (Set.range fun i =>
      KaehlerDifferential.D k (MvPolynomial (Fin m) k) (MvPolynomial.X i)) = ⊤ := by
    rw [← (KaehlerDifferential.mvPolynomialBasis k (Fin m)).span_eq]
    congr 1
    ext ω
    simp only [Set.mem_range, hb]
  rw [eq_top_iff]
  rintro ω -
  obtain ⟨z, rfl⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k
    (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭)).surjective ω
  induction z using TensorProduct.inductionOn with
  | tmul a w =>
    have hw : w ∈ Submodule.span (MvPolynomial (Fin m) k) (Set.range fun i =>
        KaehlerDifferential.D k (MvPolynomial (Fin m) k) (MvPolynomial.X i)) :=
      hspanR ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hw
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul, map_sum]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
    rw [map_smul, KaehlerDifferential.map_D, ← algebraMap_smul (Localization.AtPrime 𝔭) (c i)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | add y z hy hz =>
    rw [map_add]
    exact add_mem hy hz

end GeometricRegularity

end Langlands.CommutativeAlgebra.Popescu
