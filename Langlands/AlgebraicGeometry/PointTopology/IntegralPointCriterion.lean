import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Langlands.AlgebraicGeometry.PointTopology.AffineProductRingTopologyProof
import Mathlib.Order.Filter.Finite

/-! # Finite coordinate tests for actual affine integral points -/

noncomputable section

universe u w

open CategoryTheory AlgebraicGeometry Filter

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]
  (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
  (L : Type u) [CommRing L] [Algebra R L]

/-- An actual affine point extends to a subalgebra precisely when every
global regular function takes its value in that subalgebra. -/
theorem mem_range_changeRing_subalgebra_iff (T : Subalgebra R L)
    (p : RingPoint R X L) :
    p ∈ Set.range (RingPoint.changeRing (X := X) T.val) ↔
      ∀ a : AffineCoordinateRing R X, affineSchemePointEquiv R X L p a ∈ T := by
  constructor
  · rintro ⟨q, rfl⟩ a
    rw [affineSchemePointEquiv_changeRing]
    exact (affineSchemePointEquiv R X T q a).property
  · intro h
    let f := (affineSchemePointEquiv R X L p).toAlgHom.codRestrict T h
    let q := (affineSchemePointEquiv R X T).symm (AlgPoint.ofAlgHom f)
    refine ⟨q, ?_⟩
    apply (affineSchemePointEquiv R X L).injective
    rw [affineSchemePointEquiv_changeRing]
    change AlgPoint.mapCoefficients T.val
      ((affineSchemePointEquiv R X T)
        ((affineSchemePointEquiv R X T).symm (AlgPoint.ofAlgHom f))) = _
    rw [Equiv.apply_symm_apply]
    rfl

/-- A set of algebra generators suffices to test extension to the subalgebra. -/
theorem mem_range_changeRing_subalgebra_iff_of_adjoin_eq_top
    (s : Set (AffineCoordinateRing R X)) (hs : Algebra.adjoin R s = ⊤)
    (T : Subalgebra R L) (p : RingPoint R X L) :
    p ∈ Set.range (RingPoint.changeRing (X := X) T.val) ↔
      ∀ a ∈ s, affineSchemePointEquiv R X L p a ∈ T := by
  rw [mem_range_changeRing_subalgebra_iff]
  constructor
  · exact fun h a _ => h a
  · intro h a
    have hle : Algebra.adjoin R s ≤
        T.comap (affineSchemePointEquiv R X L p).toAlgHom :=
      Algebra.adjoin_le h
    rw [hs] at hle
    exact hle (show a ∈ (⊤ : Subalgebra R (AffineCoordinateRing R X)) from trivial)

variable [LocallyOfFiniteType X.hom]

/-- One finite set of functions tests extension for every value algebra and
every subalgebra, before either is chosen. -/
theorem exists_finset_integralPointCriterion :
    ∃ s : Finset (AffineCoordinateRing R X),
      ∀ (L : Type u) [CommRing L] [Algebra R L] (T : Subalgebra R L)
        (p : RingPoint R X L),
        p ∈ Set.range (RingPoint.changeRing (X := X) T.val) ↔
          ∀ a ∈ s, affineSchemePointEquiv R X L p a ∈ T := by
  obtain ⟨s, hs⟩ := (inferInstance :
    Algebra.FiniteType R (AffineCoordinateRing R X)).out
  exact ⟨s, fun L _ _ T p =>
    mem_range_changeRing_subalgebra_iff_of_adjoin_eq_top R X L s hs T p⟩

/-- A fixed finite test set, chosen before the value algebra and its subalgebra. -/
def integralPointTestSet : Finset (AffineCoordinateRing R X) :=
  (exists_finset_integralPointCriterion R X).choose

theorem mem_range_changeRing_subalgebra_iff_testSet
    (T : Subalgebra R L) (p : RingPoint R X L) :
    p ∈ Set.range (RingPoint.changeRing (X := X) T.val) ↔
      ∀ a ∈ integralPointTestSet R X, affineSchemePointEquiv R X L p a ∈ T :=
  (exists_finset_integralPointCriterion R X).choose_spec L T p

omit [CommRing L] [Algebra R L] in
/-- Functionwise eventual integrality, uniform over each point set, gives
eventual extension of every point in the sets to the specified subalgebras. -/
theorem eventually_range_changeRing_of_eventually_evaluation
    {ι : Type w} (l : Filter ι) (L : ι → Type u)
    [∀ i, CommRing (L i)] [∀ i, Algebra R (L i)]
    (T : ∀ i, Subalgebra R (L i)) (K : ∀ i, Set (RingPoint R X (L i)))
    (h : ∀ a : AffineCoordinateRing R X, ∀ᶠ i in l,
      ∀ p ∈ K i, affineSchemePointEquiv R X (L i) p a ∈ T i) :
    ∀ᶠ i in l, K i ⊆
      Set.range (RingPoint.changeRing (X := X) (T i).val) := by
  obtain ⟨s, hs⟩ := exists_finset_integralPointCriterion R X
  have hall : ∀ᶠ i in l, ∀ a ∈ s,
      ∀ p ∈ K i, affineSchemePointEquiv R X (L i) p a ∈ T i :=
    (eventually_all_finite s.finite_toSet).mpr (fun a _ => h a)
  filter_upwards [hall] with i hi p hp
  exact (hs (L i) (T i) p).mpr (fun a ha => hi a ha p hp)

end Langlands.AlgebraicGeometry.PointTopology
