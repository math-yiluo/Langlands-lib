import Langlands.ClassField.Global.IdeleClassNormGaloisProductStatement
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The idele-class norm as a product over embeddings

For number fields `F ⊆ K ⊆ E` and a finite family of `F`-automorphisms `s i` of `E`
whose restrictions to `K` are exactly the `F`-embeddings `K → E`, the norm
`C_K → C_F` followed by the inclusion `C_F → C_E` is the product of the `s i`-translates
of the inclusion `C_K → C_E`. The extension `K / F` need not be Galois. -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField BigOperators
open Langlands.Global.AdelicFunctoriality

universe u v w

section FieldNorm

variable (F : Type u) (K : Type v) (E : Type w) [Field F] [Field K] [Field E]
  [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]

/-- For a normal extension `E / F` containing the finite separable extension `K / F`, the
norm of `x ∈ K` is the product of its images under the `F`-embeddings `K → E`. -/
theorem algebraMap_norm_eq_prod_algHom [FiniteDimensional F K] [Algebra.IsSeparable F K]
    [Normal F E] [Fintype (K →ₐ[F] E)] (x : K) :
    algebraMap F E (Algebra.norm F x) = ∏ τ : K →ₐ[F] E, τ x := by
  classical
  let Ω := AlgebraicClosure E
  let ι : E →ₐ[F] Ω := IsScalarTower.toAlgHom F E Ω
  have hbij : Function.Bijective fun τ : K →ₐ[F] E => ι.comp τ := by
    constructor
    · intro τ₁ τ₂ hτ
      ext y
      exact (algebraMap E Ω).injective (DFunLike.congr_fun hτ y)
    · intro ρ
      have : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.tower_top (K := F) K
      obtain ⟨φ, hφ⟩ :=
        IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := F) (L := K) (M := Ω) (E := E) ρ
      refine ⟨(φ.restrictNormal' E).toAlgHom.comp (IsScalarTower.toAlgHom F K E), ?_⟩
      ext y
      have h₁ := AlgHom.restrictNormal_commutes φ E (algebraMap K E y)
      rw [Algebra.algebraMap_self, RingHom.id_apply] at h₁
      rw [← hφ]
      exact h₁
  apply (algebraMap E Ω).injective
  rw [map_prod, ← IsScalarTower.algebraMap_apply F E Ω, Algebra.norm_eq_prod_embeddings F Ω x]
  exact (Fintype.prod_bijective _ hbij _ _ fun τ => rfl).symm

/-- The field norm as a product over a family of automorphisms of `E` whose restrictions to
`K` are exactly the `F`-embeddings `K → E`. -/
theorem algebraMap_norm_eq_prod_of_bijective [FiniteDimensional F K] [Algebra.IsSeparable F K]
    [Normal F E] {I : Type*} [Fintype I] (s : I → E ≃ₐ[F] E)
    (hs : Function.Bijective fun i => (s i).toAlgHom.comp (IsScalarTower.toAlgHom F K E))
    (x : K) :
    algebraMap F E (Algebra.norm F x) = ∏ i, s i (algebraMap K E x) := by
  let _ : Fintype (K →ₐ[F] E) := Fintype.ofBijective _ hs
  rw [algebraMap_norm_eq_prod_algHom F K E x]
  exact (Fintype.prod_bijective _ hs _ _ fun i => rfl).symm

end FieldNorm

/-- Weak approximation in the unrestricted product of the actual finite completions. -/
private theorem denseRange_finiteCompletionProduct (K : Type v) [Field K] [NumberField K] :
    DenseRange (fun x : K => fun p : HeightOneSpectrum (𝓞 K) =>
      algebraMap K (p.adicCompletion K) x) := by
  classical
  have hfinite (I : Finset (HeightOneSpectrum (𝓞 K))) :
      DenseRange (fun x : K => fun p : I => algebraMap K (p.1.adicCompletion K) x) := by
    have h := AbsoluteValue.denseRange_algebraMap_pi
      (v := fun p : I => NumberField.HeightOneSpectrum.adicAbv K p.1)
      (fun p => finiteAdicAbv_isNontrivial p.1)
      (fun p q hpq h => hpq (Subtype.ext ((finiteAdicAbv_isEquiv_iff p.1 q.1).mp h)))
    exact (DenseRange.piMap (fun p : I => finiteWithAbsEmbedding_denseRange p.1)).comp h
      (.piMap fun p => (finiteWithAbsEmbedding_isometry p.1).continuous)
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨a, ha⟩ := hne
  obtain ⟨I, V, hV, hVU⟩ := isOpen_pi_iff.mp hU a ha
  have hopen : IsOpen (Set.univ.pi (fun p : I => V p.1)) :=
    isOpen_set_pi Set.finite_univ (fun p _ => (hV p.1 p.2).1)
  have hnonempty : (Set.univ.pi (fun p : I => V p.1)).Nonempty :=
    ⟨fun p => a p.1, fun p _ => (hV p.1 p.2).2⟩
  obtain ⟨x, hx⟩ := (hfinite I).exists_mem_open hopen hnonempty
  exact ⟨_, hVU (fun p hp => hx ⟨p, hp⟩ (Set.mem_univ _)), x, rfl⟩

section IdeleClass

variable {F : Type u} {K : Type v} {E : Type w} [Field F] [Field K] [Field E]
  [NumberField F] [NumberField K] [NumberField E]
  [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
  {I : Type*} [Fintype I] (s : I → E ≃ₐ[F] E)
  (hs : ∀ x : K, algebraMap F E (Algebra.norm F x) = ∏ i, s i (algebraMap K E x))

private theorem finiteNormComponent_principal' (p : HeightOneSpectrum (𝓞 F)) (x : K) :
    finiteNormComponent p (fun q => algebraMap K (q.adicCompletion K) x) =
      algebraMap F (p.adicCompletion F) (Algebra.norm F x) :=
  congrArg (fun a : AdeleRing (𝓞 F) F => a.2 p) (adeleNorm_principal (K := F) x)

omit [IsScalarTower F K E] in
include hs in
/-- The formula at one finite place `q` of `E`, on the unrestricted product of the finite
completions of `K`. -/
private theorem finite_coordinate (q : HeightOneSpectrum (𝓞 E))
    (b : (w : HeightOneSpectrum (𝓞 K)) → w.adicCompletion K) :
    FiniteExtension.completionMap (q.under (𝓞 F)) q
        (finiteNormComponent (q.under (𝓞 F)) b) =
      ∏ i, finiteCompletionEquiv (s i).toRingEquiv q
        (FiniteExtension.completionMap
          ((finitePlaceEquiv (s i).toRingEquiv q).under (𝓞 K))
          (finitePlaceEquiv (s i).toRingEquiv q)
          (b ((finitePlaceEquiv (s i).toRingEquiv q).under (𝓞 K)))) := by
  have hf : Continuous fun b : ((w : HeightOneSpectrum (𝓞 K)) → w.adicCompletion K) =>
      FiniteExtension.completionMap (q.under (𝓞 F)) q
        (finiteNormComponent (q.under (𝓞 F)) b) :=
    (FiniteExtension.continuous_completionMap _ q).comp (continuous_finiteNormComponent _)
  have hg : Continuous fun b : ((w : HeightOneSpectrum (𝓞 K)) → w.adicCompletion K) =>
      ∏ i, finiteCompletionEquiv (s i).toRingEquiv q
        (FiniteExtension.completionMap
          ((finitePlaceEquiv (s i).toRingEquiv q).under (𝓞 K))
          (finitePlaceEquiv (s i).toRingEquiv q)
          (b ((finitePlaceEquiv (s i).toRingEquiv q).under (𝓞 K)))) :=
    continuous_finsetProd _ fun i _ =>
      (continuous_finiteCompletionEquiv _ q).comp
        ((FiniteExtension.continuous_completionMap _ _).comp (continuous_apply _))
  have h := (denseRange_finiteCompletionProduct K).equalizer hf hg (by
    funext x
    dsimp only [Function.comp_apply]
    rw [finiteNormComponent_principal', FiniteExtension.completionMap_coe, hs, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [FiniteExtension.completionMap_coe, finiteCompletionEquiv_coe]
    rfl)
  exact congrFun h b

omit [IsScalarTower F K E] in
include hs in
/-- The formula on infinite adeles, by density of `K` in `K ⊗ ℝ`. -/
private theorem infinite_part (b : InfiniteAdeleRing K) :
    infiniteAdeleMap (algebraMap F E) (infiniteAdeleNorm (K := F) b) =
      ∏ i, infiniteAdeleEquiv (s i).toRingEquiv (infiniteAdeleMap (algebraMap K E) b) := by
  have h := (InfiniteAdeleRing.denseRange_algebraMap K).equalizer
    ((continuous_infiniteAdeleMap (algebraMap F E)).comp
      (continuous_infiniteAdeleNorm (K := F) (L := K)))
    (continuous_finsetProd Finset.univ fun i _ =>
      (continuous_infiniteAdeleEquiv (s i).toRingEquiv).comp
        (continuous_infiniteAdeleMap (algebraMap K E)))
    (by
      funext x
      have hn : infiniteAdeleNorm (K := F) (algebraMap K (InfiniteAdeleRing K) x) =
          algebraMap F (InfiniteAdeleRing F) (Algebra.norm F x) :=
        congrArg Prod.fst (adeleNorm_principal (K := F) x)
      dsimp only [Function.comp_apply]
      rw [hn, infiniteAdeleMap_diagonal, infiniteAdeleMap_diagonal, hs, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      exact (infiniteAdeleEquiv_diagonal (s i).toRingEquiv _).symm)
  exact congrFun h b

omit [IsScalarTower F K E] in
include hs in
private theorem adele_part (b : AdeleRing (𝓞 K) K) :
    adeleInclusion (K := F) (L := E) (adeleNorm (K := F) b) =
      ∏ i, adeleEquiv (s i).toRingEquiv (adeleInclusion (K := K) (L := E) b) := by
  apply Prod.ext
  · exact (infinite_part s hs b.1).trans
      (map_prod (MonoidHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
        (fun i => adeleEquiv (s i).toRingEquiv (adeleInclusion (K := K) (L := E) b))
        Finset.univ).symm
  · have h : finiteAdeleInclusion (K := F) (L := E) (finiteAdeleNorm (K := F) b.2) =
        ∏ i, finiteAdeleEquiv (s i).toRingEquiv
          (finiteAdeleInclusion (K := K) (L := E) b.2) := by
      apply FiniteAdeleRing.ext
      intro q
      exact (finite_coordinate s hs q b.2).trans
        (map_prod (RestrictedProduct.evalMonoidHom _ q)
          (fun i => finiteAdeleEquiv (s i).toRingEquiv
            (finiteAdeleInclusion (K := K) (L := E) b.2)) Finset.univ).symm
    exact h.trans
      (map_prod (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
        (fun i => adeleEquiv (s i).toRingEquiv (adeleInclusion (K := K) (L := E) b))
        Finset.univ).symm

omit [IsScalarTower F K E] in
include hs in
/-- If the field norm `K → F` is the product of the automorphisms `s i` on `K ⊆ E`, then the
idele-class norm `C_K → C_F`, followed by the inclusion into `C_E`, is the product of the
`s i`-translates of the inclusion `C_K → C_E`. -/
theorem ideleClassInclusion_ideleClassNorm_eq_prod_of_norm (x : IdeleClassGroup (𝓞 K) K) :
    ideleClassInclusion (K := F) (L := E) (ideleClassNorm (K := F) (L := K) x) =
      ∏ i, relativeIdeleClassAut F E (s i) (ideleClassInclusion (K := K) (L := E) x) := by
  refine QuotientGroup.induction_on x fun a => ?_
  rw [ideleClassNorm_mk, ideleClassInclusion_mk, ideleClassInclusion_mk]
  have h : ideleInclusion (K := F) (L := E) (ideleNorm (K := F) a) =
      ∏ i, ideleEquiv (s i).toRingEquiv (ideleInclusion (K := K) (L := E) a) := by
    apply Units.ext
    change adeleInclusion (adeleNorm (K := F) a.val) =
      (Units.coeHom _) (∏ i, ideleEquiv (s i).toRingEquiv (ideleInclusion (K := K) (L := E) a))
    rw [map_prod]
    exact adele_part s hs a.val
  rw [h]
  exact map_prod (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 E) E)) _ _

end IdeleClass

/-- The idele-class norm as a product over embeddings. Let `F ⊆ K ⊆ E` be number fields
with `E / F` normal, and let `s : I → (E ≃ₐ[F] E)` be a finite family whose restrictions
to `K` are exactly the `F`-embeddings `K → E`, each once. Then the inclusion of
`N_{K/F} x` into `C_E` is the product of the `s i`-translates of the inclusion of `x`. -/
theorem ideleClassInclusion_ideleClassNorm_eq_prod {F : Type u} {K : Type v} {E : Type w}
    [Field F] [Field K] [Field E] [NumberField F] [NumberField K] [NumberField E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E] [Normal F E]
    {I : Type*} [Fintype I] (s : I → E ≃ₐ[F] E)
    (hs : Function.Bijective fun i => (s i).toAlgHom.comp (IsScalarTower.toAlgHom F K E))
    (x : IdeleClassGroup (𝓞 K) K) :
    ideleClassInclusion (K := F) (L := E) (ideleClassNorm (K := F) (L := K) x) =
      ∏ i, relativeIdeleClassAut F E (s i) (ideleClassInclusion (K := K) (L := E) x) :=
  ideleClassInclusion_ideleClassNorm_eq_prod_of_norm s
    (algebraMap_norm_eq_prod_of_bijective F K E s hs) x

end Langlands.ClassField.Global
