import Langlands.Algebra.HopfPointWeightWindow
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-! # Extensions of Hopf points on principal opens where the weights lie in a window -/

noncomputable section

open TensorProduct

namespace Langlands.Algebra.HopfPointWindowExtension

open HopfPointExtension HopfPointWeightWindow

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Bialgebra R A]
  {C : Type*} [CommRing C] [Algebra R C] {D : Type*} [CommRing D] [Algebra R D]
  {M : Type*} [AddCommGroup M]

section CoefficientChange

variable (ψ : C →ₐ[R] D)

theorem groupCounit_comp_mapAlgHom :
    (groupCounit R D M).comp (AddMonoidAlgebra.mapAlgHom M ψ) = ψ.comp (groupCounit R C M) := by
  apply AlgHom.ext
  intro x
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m c => simp [groupCounit, AddMonoidAlgebra.lift_single]

theorem mapAlgHom_comp_mapDomain {N : Type*} [AddCommGroup N] (π : M →+ N) :
    (AddMonoidAlgebra.mapAlgHom N ψ).comp (AddMonoidAlgebra.mapDomainAlgHom R C π) =
      (AddMonoidAlgebra.mapDomainAlgHom R D π).comp (AddMonoidAlgebra.mapAlgHom M ψ) := by
  apply AlgHom.ext
  intro x
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m c => simp

theorem mapAlgHom_comp_pairMap (f : A →ₐ[R] AddMonoidAlgebra C M) :
    (AddMonoidAlgebra.mapAlgHom (M × M) ψ).comp (pairMap f) =
      pairMap ((AddMonoidAlgebra.mapAlgHom M ψ).comp f) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp only [pairMap, AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul, map_mul]
  rw [← AlgHom.comp_apply _ (inlMap R C M), inlMap, mapAlgHom_comp_mapDomain,
    ← AlgHom.comp_apply _ (inrMap R C M), inrMap, mapAlgHom_comp_mapDomain]
  rfl

/-- Hopf points push forward along changes of coefficients. -/
theorem IsHopfPoint.mapAlgHom {f : A →ₐ[R] AddMonoidAlgebra C M} (hf : IsHopfPoint f) :
    IsHopfPoint ((AddMonoidAlgebra.mapAlgHom M ψ).comp f) where
  comul := by
    rw [← mapAlgHom_comp_pairMap, AlgHom.comp_assoc, hf.comul, ← AlgHom.comp_assoc, diagMap,
      mapAlgHom_comp_mapDomain, AlgHom.comp_assoc, diagMap]
  counit := by
    rw [← AlgHom.comp_assoc, groupCounit_comp_mapAlgHom, AlgHom.comp_assoc, hf.counit,
      ← AlgHom.comp_assoc]
    congr 1
    exact AlgHom.ext fun x => (ψ.commutes x)

end CoefficientChange

section Window

variable {M' : Type*} [AddCommGroup M'] {σ : Type*}

/-- Coefficients outside a window vanish after inverting one element outside `p`,
when the weights at the residue field of `p` lie in the window. -/
theorem exists_away_support_subset (V : Submodule R A) [Module.Finite R V]
    (δ : V →ₗ[R] V ⊗[R] A) (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := A)) ∘ₗ V.subtype = V.subtype.rTensor A ∘ₗ δ)
    {β : A →ₐ[R] AddMonoidAlgebra C M'} (hβ : IsHopfPoint β) (T : Set M')
    (p : Ideal C) [p.IsPrime]
    (hwin : WeightsIn δ ((AddMonoidAlgebra.mapAlgHom M'
      (IsScalarTower.toAlgHom R C p.ResidueField)).comp β) T) :
    ∃ f ∉ p, ∀ v ∈ V, ↑((AddMonoidAlgebra.mapAlgHom M'
      (IsScalarTower.toAlgHom R C (Localization.Away f))) (β v)).coeff.support ⊆ T := by
  classical
  obtain ⟨T₀, hT₀⟩ := exists_finite_weightsIn δ β
  let L := T₀.filter (· ∉ T)
  have hL : ∀ l ∈ L, ∃ g ∉ p, ∀ v : V, g * (β (V.subtype v)).coeff l = 0 := by
    intro l hl
    have hlT : l ∉ T := (Finset.mem_filter.mp hl).2
    exact exists_mul_coeff_eq_zero δ β l hδ hβ V.subtype hι p (hwin l hlT)
  choose! g hgp hg using hL
  let f := ∏ l ∈ L, g l
  have hfp : f ∉ p := by
    simp only [f]
    intro hmem
    obtain ⟨l, hl, hlp⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hgp l hl hlp
  refine ⟨f, hfp, fun v hv => ?_⟩
  intro l hl
  by_contra hlT
  apply Finsupp.mem_support_iff.mp hl
  rw [AddMonoidAlgebra.coeff_mapAlgHom, IsScalarTower.coe_toAlgHom']
  by_cases hlT₀ : l ∈ T₀
  · have hlL : l ∈ L := Finset.mem_filter.mpr ⟨hlT₀, hlT⟩
    have hunit : IsUnit (algebraMap C (Localization.Away f) (g l)) := by
      apply isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem g hlL))
      exact IsLocalization.Away.algebraMap_isUnit f
    have h0 := congrArg (algebraMap C (Localization.Away f)) (hg l hlL ⟨v, hv⟩)
    rw [map_mul, map_zero] at h0
    exact (hunit.mul_right_eq_zero).mp h0
  · have : (β v).coeff l = 0 := by
      have := counitV_proj (C := C) δ β l V.subtype hι ⟨v, hv⟩
      rw [hT₀ l (by exact_mod_cast hlT₀), map_zero] at this
      exact this.symm
    rw [this, map_zero]

/-- The window extension: if the weights at the residue field of `p` lie in
`π '' s`, then after inverting one element outside `p` the Hopf point extends
uniquely to a Hopf point of `M` with generator values supported in `s`. -/
theorem exists_away_extension (V : Submodule R A) [Module.Finite R V]
    (δ : V →ₗ[R] V ⊗[R] A) (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := A)) ∘ₗ V.subtype = V.subtype.rTensor A ∘ₗ δ)
    {gen : σ → A} (hgenV : ∀ i, gen i ∈ V) {N : ℕ}
    (hP : IsBoundedPresentation (R := R) gen N) (hN : 1 ≤ N)
    (π : M →+ M') {s : Set M} (hπ : Set.InjOn π (boundedSums s N))
    {β : A →ₐ[R] AddMonoidAlgebra C M'} (hβ : IsHopfPoint β) (p : Ideal C) [p.IsPrime]
    (hwin : WeightsIn δ ((AddMonoidAlgebra.mapAlgHom M'
      (IsScalarTower.toAlgHom R C p.ResidueField)).comp β) (π '' s)) :
    ∃ f ∉ p, ∃! α : A →ₐ[R] AddMonoidAlgebra (Localization.Away f) M, IsHopfPoint α ∧
      (∀ i, ↑(α (gen i)).coeff.support ⊆ s) ∧
      (AddMonoidAlgebra.mapDomainAlgHom R (Localization.Away f) π).comp α =
        (AddMonoidAlgebra.mapAlgHom M'
          (IsScalarTower.toAlgHom R C (Localization.Away f))).comp β := by
  obtain ⟨f, hfp, hsupp⟩ := exists_away_support_subset V δ hδ hι hβ (π '' s) p hwin
  refine ⟨f, hfp, ?_⟩
  exact existsUnique_hopfPoint_extension hP hN π hπ
    (IsHopfPoint.mapAlgHom (IsScalarTower.toAlgHom R C (Localization.Away f)) hβ)
    (fun i => hsupp (gen i) (hgenV i))

end Window

section Presentation

variable {σ : Type*} [Finite σ]

/-- Over a noetherian ring, finitely many algebra generators of a bialgebra have a
degree bound for their relations and comultiplications. -/
theorem exists_isBoundedPresentation [IsNoetherianRing R] {gen : σ → A}
    (hgen : Algebra.adjoin R (Set.range gen) = ⊤) :
    ∃ N, 1 ≤ N ∧ IsBoundedPresentation (R := R) gen N := by
  classical
  have := Fintype.ofFinite σ
  let φ : MvPolynomial σ R →ₐ[R] A := MvPolynomial.aeval gen
  have hφ : Function.Surjective φ := by
    intro a
    have ha : a ∈ φ.range := by
      rw [MvPolynomial.aeval_range, hgen]; trivial
    obtain ⟨p, rfl⟩ := ha
    exact ⟨p, rfl⟩
  let pre : A → MvPolynomial σ R := Function.surjInv hφ
  have hpre : ∀ a, φ (pre a) = a := Function.surjInv_eq hφ
  -- relations: the kernel is finitely generated
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian (RingHom.ker φ) : (RingHom.ker φ).FG)
  -- comultiplication of the generators as finite sums of pure tensors
  choose S hS using fun i => TensorProduct.exists_finset (Bialgebra.comulAlgHom R A (gen i))
  let N₀ := t.sup MvPolynomial.totalDegree
  let N₁ := Finset.univ.sup fun i =>
    (S i).sup fun q => max (pre q.1).totalDegree (pre q.2).totalDegree
  refine ⟨max 1 (max N₀ N₁), le_max_left _ _, ⟨hgen, ?_, ?_⟩⟩
  · rw [← ht, Ideal.span_le]
    intro q hq
    refine Ideal.subset_span ⟨?_, ?_⟩
    · have : q ∈ RingHom.ker φ := ht ▸ Ideal.subset_span hq
      exact this
    · exact le_trans (Finset.le_sup (f := MvPolynomial.totalDegree) hq)
        (le_trans (le_max_left _ _) (le_max_right _ _))
  · intro i
    rw [hS i]
    refine Submodule.sum_mem _ fun q hq => Submodule.subset_span ⟨pre q.1, pre q.2, ?_, ?_, ?_⟩
    · refine le_trans ?_ (le_trans (le_max_right N₀ N₁) (le_max_right _ _))
      refine le_trans (le_max_left _ (pre q.2).totalDegree) ?_
      refine le_trans (Finset.le_sup (f := fun q : A × A =>
        max (pre q.1).totalDegree (pre q.2).totalDegree) hq) ?_
      exact Finset.le_sup (f := fun i => (S i).sup fun q : A × A =>
        max (pre q.1).totalDegree (pre q.2).totalDegree) (Finset.mem_univ i)
    · refine le_trans ?_ (le_trans (le_max_right N₀ N₁) (le_max_right _ _))
      refine le_trans (le_max_right (pre q.1).totalDegree _) ?_
      refine le_trans (Finset.le_sup (f := fun q : A × A =>
        max (pre q.1).totalDegree (pre q.2).totalDegree) hq) ?_
      exact Finset.le_sup (f := fun i => (S i).sup fun q : A × A =>
        max (pre q.1).totalDegree (pre q.2).totalDegree) (Finset.mem_univ i)
    · change q.1 ⊗ₜ[R] q.2 = φ (pre q.1) ⊗ₜ[R] φ (pre q.2)
      rw [hpre, hpre]

end Presentation

end Langlands.Algebra.HopfPointWindowExtension
