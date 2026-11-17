import Langlands.AlgebraicGeometry.SmoothDvrAffineOpenGeometry
import Langlands.AlgebraicGeometry.FibreGenericPoints
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes

/-! # A finite set of codimension-at-most-one points meeting every DVR fibre component -/

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

noncomputable section

namespace Langlands.AlgebraicGeometry

namespace SmoothDvrFibreGenericPoints

lemma finite_base (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : Finite (Spec (CommRingCat.of R)) := by
  apply Finite.of_finite_univ
  apply (Set.toFinite ({(⟨⊥, inferInstance⟩ : PrimeSpectrum R), IsLocalRing.closedPoint R})).subset
  intro s _
  rcases SmoothDvrAffineOpenGeometry.point_eq_generic_or_closed R s with h | h <;> simp [h]

lemma noProperGenerization_in_fibre {X S : Scheme.{u}} (p : X ⟶ S) (s : S)
    (z : p.fiber s) (hz : z ∈ genericPoints (p.fiber s))
    (y : X) (hy : y ⤳ p.fiberι s z) (hpy : p y = s) :
    y = p.fiberι s z := by
  let w := (p.fiberHomeo s).symm ⟨y, hpy⟩
  have hw : p.fiberι s w = y := p.fiberι_fiberHomeo_symm s _
  have hwz : w ⤳ z := (p.fiberι s).isEmbedding.specializes_iff.mp (hw ▸ hy)
  exact hw.symm.trans (congrArg (p.fiberι s)
    (GenericPointAvoidance.mem_genericPoints_iff.mp hz _ hwz))

/-- All generic points of fibres of a smooth DVR scheme have stalk dimension at most one. -/
theorem ringKrullDim_stalk_le_one
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of R)) [Smooth p]
    (x : X) (hx : x ∈ fibreGenericPoints p) :
    ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  obtain ⟨s, z, hz, rfl⟩ := Set.mem_iUnion.mp hx
  have hps : p (p.fiberι s z) = s := (p.fiberHomeo s z).2
  rcases SmoothDvrAffineOpenGeometry.point_eq_generic_or_closed R s with hs | hs
  · subst s
    have hgeneric : p.fiberι (⟨⊥, inferInstance⟩ : PrimeSpectrum R) z ∈ genericPoints X := by
      apply GenericPointAvoidance.mem_genericPoints_iff.mpr
      intro y hy
      apply noProperGenerization_in_fibre p _ z hz y hy
      have hle := (PrimeSpectrum.le_iff_specializes _ _).mpr (hy.map p.continuous)
      rw [hps] at hle
      exact PrimeSpectrum.ext (le_bot_iff.mp hle)
    have (y : X) : IsDomain (X.presheaf.stalk y) :=
      (Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R p y).1
    have : ∀ y : X, _root_.IsReduced (X.presheaf.stalk y) := fun _ => inferInstance
    have : IsReduced X := isReduced_of_isReduced_stalk X
    rw [ringKrullDim_eq_zero_of_isField
      (isField_stalk_of_closure_mem_irreducibleComponents X _ hgeneric)]
    exact zero_le_one
  · obtain ⟨hdom, hdvr⟩ := Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R p
      (p.fiberι s z) (hps.trans hs) (fun y hy hpy =>
        noProperGenerization_in_fibre p s z hz y hy (hpy.trans hs.symm))
    let := hdom
    let := hdvr
    exact Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 _)

end SmoothDvrFibreGenericPoints

/-- The finite family of points to which the common affine neighbourhood theorem applies. -/
def smoothDvrFibreGenericPoints
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of R)) [Smooth p] [QuasiCompact p] :
    Finset X :=
  letI := SmoothDvrFibreGenericPoints.finite_base R
  (finite_fibreGenericPoints p).toFinset

@[simp]
theorem mem_smoothDvrFibreGenericPoints
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of R)) [Smooth p] [QuasiCompact p]
    (x : X) : x ∈ smoothDvrFibreGenericPoints R X p ↔ x ∈ fibreGenericPoints p := by
  simp [smoothDvrFibreGenericPoints]

theorem smoothDvrFibreGenericPoints_dim_le_one
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of R)) [Smooth p] [QuasiCompact p]
    (x : X) (hx : x ∈ smoothDvrFibreGenericPoints R X p) :
    ringKrullDim (X.presheaf.stalk x) ≤ 1 :=
  SmoothDvrFibreGenericPoints.ringKrullDim_stalk_le_one R X p x
    ((mem_smoothDvrFibreGenericPoints R X p x).mp hx)

theorem fibreGenerizationDense_of_smoothDvrFibreGenericPoints_subset
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of R)) [Smooth p] [QuasiCompact p]
    (U : Set X) (hU : ∀ x ∈ smoothDvrFibreGenericPoints R X p, x ∈ U) :
    FibreGenerizationDense p U := by
  apply (fibreGenericPoints_subset_iff p U).mp
  intro x hx
  exact hU x ((mem_smoothDvrFibreGenericPoints R X p x).mpr hx)

end Langlands.AlgebraicGeometry
