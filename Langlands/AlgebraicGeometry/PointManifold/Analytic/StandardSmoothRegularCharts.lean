import Langlands.AlgebraicGeometry.PointManifold.Analytic.SubmersivePresentationCharts

/-! # Analytic Regular charts on standard-smooth actual affine point spaces -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped ContDiff Classical

namespace Langlands.AlgebraicGeometry.PointManifold.Analytic

open PointTopology

private def splitInjectionEquiv {ι σ : Type*} (f : σ → ι) (hf : Function.Injective f) :
    {i : ι // i ∉ Set.range f} ⊕ σ ≃ ι :=
  Equiv.ofBijective (Sum.elim Subtype.val f) (by
    constructor
    · intro x y h
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (Subtype.ext h)
        | inr y => exact (x.property ⟨y, h.symm⟩).elim
      | inr x =>
        cases y with
        | inl y => exact (y.property ⟨x, h⟩).elim
        | inr y => exact congrArg Sum.inr (hf h)
    · intro i
      by_cases hi : i ∈ Set.range f
      · obtain ⟨j, rfl⟩ := hi
        exact ⟨Sum.inr j, rfl⟩
      · exact ⟨Sum.inl ⟨i, hi⟩, rfl⟩)

private theorem exists_submersiveVariableEquiv
    {k A ι σ : Type*} [CommRing k] [CommRing A] [Algebra k A]
    [Fintype ι] [Fintype σ] (P : Algebra.SubmersivePresentation k A ι σ)
    {d : ℕ} (hd : P.dimension = d) :
    ∃ e : Fin d ⊕ σ ≃ ι, ∀ j, e (Sum.inr j) = P.map j := by
  classical
  let τ := {i : ι // i ∉ Set.range P.map}
  let e := splitInjectionEquiv P.map P.map_inj
  have hcard : Fintype.card τ = d := by
    have hc := Fintype.card_congr e
    have hd' : Fintype.card ι - Fintype.card σ = d := by
      simpa only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] using hd
    simp only [Fintype.card_sum] at hc
    change Fintype.card τ + Fintype.card σ = Fintype.card ι at hc
    omega
  refine ⟨(Equiv.sumCongr (Fintype.equivFinOfCardEq hcard).symm (Equiv.refl σ)).trans e, ?_⟩
  intro j
  rfl

variable {k : Type u} [NontriviallyNormedField k] [CompleteSpace k]
variable {X : Over (Spec (CommRingCat.of k))} [IsAffine X.left] {d : ℕ}

/-- Algebraic standard smoothness supplies an actual regular chart at every point. -/
theorem exists_regularChart_of_standardSmooth
    (h : Algebra.IsStandardSmoothOfRelativeDimension d k (AffineCoordinateRing k X))
    (p : RingPoint k X k) :
    ∃ C : RegularChart k X d, p ∈ C.homeomorph.source := by
  rcases h.out with ⟨ι, σ, hσ, hι, P, hd⟩
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype σ := Fintype.ofFinite σ
  obtain ⟨e, he⟩ := exists_submersiveVariableEquiv P hd
  let Q := P.reindex e (Equiv.refl σ)
  have hmap : ∀ j, Q.map j = Sum.inr j := by
    intro j
    change e.symm (P.map j) = Sum.inr j
    rw [← he j, e.symm_apply_apply]
  exact ⟨RegularChart.ofSubmersivePresentation Q hmap p,
    RegularChart.mem_ofSubmersivePresentation_source Q hmap p⟩

/-- Choose the regular chart supplied by standard smoothness of the actual coordinate algebra. -/
def RegularChart.ofStandardSmooth
    (h : Algebra.IsStandardSmoothOfRelativeDimension d k (AffineCoordinateRing k X))
    (p : RingPoint k X k) : RegularChart k X d :=
  Classical.choose (exists_regularChart_of_standardSmooth h p)

theorem RegularChart.mem_ofStandardSmooth_source
    (h : Algebra.IsStandardSmoothOfRelativeDimension d k (AffineCoordinateRing k X))
    (p : RingPoint k X k) :
    p ∈ (RegularChart.ofStandardSmooth h p).homeomorph.source :=
  Classical.choose_spec (exists_regularChart_of_standardSmooth h p)

end Langlands.AlgebraicGeometry.PointManifold.Analytic
