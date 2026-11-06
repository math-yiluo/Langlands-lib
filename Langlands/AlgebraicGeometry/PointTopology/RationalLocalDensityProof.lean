import Langlands.AlgebraicGeometry.PointTopology.RationalLocalDensityStatement
import Langlands.AlgebraicGeometry.PointTopology.SmoothOpenMapProof
import Langlands.AlgebraicGeometry.PointTopology.AdicSmoothPointLifting
import Langlands.RingTheory.LocalFieldDensity.LocalSeparationProof

/-! # Local Zariski density through the actual affine point comparisons -/

noncomputable section

universe u v

open CategoryTheory Filter Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

section AlgebraPoints

variable {K : Type u} [NontriviallyNormedField K]
  {A : Type v} [CommRing A] [Algebra K A]

/-- The prime ideal of an actual algebra point is the inverse image of the
unique field-spectrum point. -/
def algPointSpectrum (p : AlgPoint K A K) : PrimeSpectrum A :=
  PrimeSpectrum.comap p.toAlgHom.toRingHom (IsLocalRing.closedPoint K)

@[simp] theorem algPointSpectrum_mem_basicOpen (p : AlgPoint K A K) (a : A) :
    algPointSpectrum p ∈ PrimeSpectrum.basicOpen a ↔ p a ≠ 0 := by
  simp [algPointSpectrum, PrimeSpectrum.mem_basicOpen, IsLocalRing.closedPoint,
    IsLocalRing.maximalIdeal_eq_bot]

theorem continuous_algPointSpectrum :
    Continuous (algPointSpectrum : AlgPoint K A K → PrimeSpectrum A) := by
  apply PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff.mpr
  rintro _ ⟨a, rfl⟩
  have heq : algPointSpectrum ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) =
      {p : AlgPoint K A K | p a ≠ 0} := by
    ext p
    exact algPointSpectrum_mem_basicOpen p a
  rw [heq]
  exact isOpen_ne_fun (AlgPoint.continuous_eval a) continuous_const

theorem dense_algPointSpectrum_image_of_isOpen [CompleteSpace K]
    [Algebra.Smooth K A] [IsDomain A]
    (U : Set (AlgPoint K A K)) (hU : IsOpen U) (hne : U.Nonempty) :
    Dense (algPointSpectrum '' U) := by
  apply PrimeSpectrum.isTopologicalBasis_basic_opens.dense_iff.mpr
  rintro _ ⟨a, rfl⟩ ⟨p, hp⟩
  have ha : a ≠ 0 := by
    intro h
    simp [h] at hp
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hyU, hya⟩ :=
    Langlands.RingTheory.LocalFieldDensity.exists_algPoint_mem_apply_ne_zero
      x.toAlgHom U (hU.mem_nhds hx) ha
  exact ⟨algPointSpectrum y, (algPointSpectrum_mem_basicOpen y a).mpr hya,
    y, hyU, rfl⟩

end AlgebraPoints

/-- The complete local-density proposition for actual affine rational points. -/
theorem rationalLocalDensity : RationalLocalDensityStatement.{u} := by
  intro F _ _ _ _ X _ _ _
  let _ := Langlands.LocalGalois.localNormedField F
  have := Langlands.LocalGalois.localNormedField_complete F
  let : TopologicalSpace (RationalPoint F X) := rationalPointTopology F X
  let : IsDomain (AffineCoordinateRing F X) :=
    inferInstanceAs (IsDomain Γ(X.left, ⊤))
  let := smooth_affineCoordinateRing F X
  let e := affineRationalPointHomeomorph F X
  let s : X.left ≃ₜ PrimeSpectrum (AffineCoordinateRing F X) :=
    Scheme.homeoOfIso X.left.isoSpec
  have heval (p : RationalPoint F X) :
      algPointSpectrum (e p) = s (p.left (IsLocalRing.closedPoint F)) := by
    have h := affineSchemePointEquiv_spec F F (rationalPointEquiv F X p)
    rw [rationalPointEquiv_left] at h
    have hp := congrArg (fun f => f (IsLocalRing.closedPoint F)) h
    change algPointSpectrum (e p) = s (p.left (IsLocalRing.closedPoint F)) at hp
    exact hp
  have heq : (fun p : RationalPoint F X => p.left (IsLocalRing.closedPoint F)) =
      s.symm ∘ algPointSpectrum (A := AffineCoordinateRing F X) ∘ e := by
    funext p
    simp only [Function.comp_apply, heval, Homeomorph.symm_apply_apply]
  constructor
  · rw [heq]
    exact s.symm.continuous.comp
      ((continuous_algPointSpectrum (A := AffineCoordinateRing F X)).comp e.continuous)
  · intro U hU hne
    have hd := dense_algPointSpectrum_image_of_isOpen (e '' U)
      (e.isOpenMap U hU) (hne.image e)
    have hd' := s.symm.surjective.denseRange.dense_image s.symm.continuous hd
    rw [Set.image_image, Set.image_image] at hd'
    rw [heq]
    exact hd'

end Langlands.AlgebraicGeometry.PointTopology
