import Langlands.AlgebraicGeometry.UniformLangWeilRationalSections
import Langlands.AlgebraicGeometry.NoetherianApproximation.ClosedFiberPolynomialCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Jacobson.Ring

/-! # Transporting closed-fibre rational sections to finite-field-valued points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A finite-field-valued point of a scheme locally of finite type over the
integers has closed image. -/
theorem isClosed_image_of_finite_field
    {B : Scheme.{u}} (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B))
    (K : Type u) [Field K] [Finite K] (p : Spec (CommRingCat.of K) ⟶ B) :
    IsClosed ({p (IsLocalRing.closedPoint K)} : Set B) := by
  let := hBft
  let : IsJacobsonRing (ULift.{u} ℤ) :=
    (isJacobsonRing_iso ULift.ringEquiv).2 NoetherianApproximation.isJacobsonRing_int
  let : JacobsonSpace B := LocallyOfFiniteType.jacobsonSpace
    (specULiftZIsTerminal.{u}.from B)
  have hKft : LocallyOfFiniteType
      (specULiftZIsTerminal.{u}.from (Spec (CommRingCat.of K))) := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective
      (specULiftZIsTerminal.{u}.from (Spec (CommRingCat.of K)))
    rw [← hφ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    let := φ.hom.toAlgebra
    change Algebra.FiniteType (ULift.{u} ℤ) K
    infer_instance
  have hcomp : LocallyOfFiniteType (p ≫ specULiftZIsTerminal.{u}.from B) := by
    convert hKft using 1
    exact specULiftZIsTerminal.{u}.hom_ext _ _
  let : LocallyOfFiniteType p := locallyOfFiniteType_of_comp p
    (specULiftZIsTerminal.{u}.from B)
  exact p.closePoints_subset_preimage_closedPoints
    (IsLocalRing.isClosed_singleton_closedPoint K)

/-- Extending a rational section of the residue fibre along the actual
residue-field embedding gives a lift of the original field-valued point. -/
def liftFieldPointFromResidueSection
    {B Y : Scheme.{u}} (f : Y ⟶ B) (K : Type u) [Field K]
    (p : Spec (CommRingCat.of K) ⟶ B)
    (s : {s : Spec (B.residueField (p (IsLocalRing.closedPoint K))) ⟶
        f.fiber (p (IsLocalRing.closedPoint K)) //
      s ≫ f.fiberToSpecResidueField (p (IsLocalRing.closedPoint K)) = 𝟙 _}) :
    {q : Spec (CommRingCat.of K) ⟶ Y // q ≫ f = p} := by
  let φ := B.descResidueField (Scheme.stalkClosedPointTo p)
  refine ⟨Spec.map φ ≫ s.1 ≫ f.fiberι (p (IsLocalRing.closedPoint K)), ?_⟩
  rw [Category.assoc, Category.assoc, Scheme.Hom.fiber_fac,
    ← Category.assoc s.1, s.2, Category.id_comp]
  exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K B p

/-- The residue field of the image embeds in the finite field of values. -/
theorem finite_residueField_of_fieldPoint
    {B : Scheme.{u}} (K : Type u) [Field K] [Finite K]
    (p : Spec (CommRingCat.of K) ⟶ B) :
    Finite (B.residueField (p (IsLocalRing.closedPoint K))) :=
  Finite.of_injective (B.descResidueField (Scheme.stalkClosedPointTo p)).hom
    (RingHom.injective _)

/-- The residue field of the image has cardinality at most the field of values. -/
theorem card_residueField_le_of_fieldPoint
    {B : Scheme.{u}} (K : Type u) [Field K] [Finite K]
    (p : Spec (CommRingCat.of K) ⟶ B) :
    Nat.card (B.residueField (p (IsLocalRing.closedPoint K))) ≤ Nat.card K := by
  exact Nat.card_le_card_of_injective
    (B.descResidueField (Scheme.stalkClosedPointTo p)).hom (RingHom.injective _)

/-- The uniform estimate constructs a lift of each finite-field-valued point
whose image has sufficiently large residue field. -/
def uniformLangWeilLargeResidueFieldPointLifts
    (hLW : UniformLangWeilStatement.{u})
    (B Y : Scheme.{u}) (f : Y ⟶ B) (d : ℕ)
    (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B))
    (hBqc : CompactSpace B) (hsmooth : Smooth f)
    (hsep : _root_.AlgebraicGeometry.IsSeparated f) (hsurj : Surjective f)
    (hft : LocallyOfFiniteType f) (hqc : QuasiCompact f)
    (hconn : GeometricallyConnected f)
    (hdim : ∀ b : B, SchemeFiberGeometry.HasPureDimension (f.fiber b) d) :
    Σ C : {C : ℝ // 0 < C},
      (K : Type u) → [Field K] → [Finite K] →
        (p : Spec (CommRingCat.of K) ⟶ B) →
        C.1 ^ 2 < (Nat.card (B.residueField (p (IsLocalRing.closedPoint K))) : ℝ) →
        {q : Spec (CommRingCat.of K) ⟶ Y // q ≫ f = p} := by
  classical
  let sections := uniformLangWeilLargeResidueSections hLW B Y f d hBft hBqc
    hsmooth hsep hsurj hft hqc hconn hdim
  refine ⟨sections.1, fun K _ _ p hlarge => ?_⟩
  exact liftFieldPointFromResidueSection f K p
    (sections.2 _ (isClosed_image_of_finite_field hBft K p) hlarge)

end Langlands.AlgebraicGeometry
