import Langlands.GroupScheme.Rational.CocharacterCone
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # The nonnegative common-uniformizer monoid and its quotient image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterUniformizer

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (R : Set (characterLattice T))

/-- The nonnegative common-uniformizer monoid in the actual rational points. -/
def CAplusMonoid : Submonoid (rationalPoints T.toGrp) :=
  (AddSubmonoid.toSubmonoid (CocharacterCone.nonnegative T R)).map
    (latticeSection F T)

/-- The new submonoid has precisely the already defined `C_T^+` as carrier. -/
@[simp] theorem mem_CAplusMonoid (a : rationalPoints T.toGrp) :
    a ∈ CAplusMonoid F T R ↔ a ∈ CAplus F T R := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact (CocharacterCone.latticeSection_mem_CAplus_iff T R c.toAdd).mpr hc
  · rintro ⟨⟨c, rfl⟩, hc⟩
    refine ⟨c, ?_, rfl⟩
    exact (CocharacterCone.latticeSection_mem_CAplus_iff T R c.toAdd).mp
      ⟨⟨c, rfl⟩, hc⟩

variable (A : CommGroupScheme (Spec (CommRingCat.of F))) (f : A ⟶ T)

/-- The image of `C_T^+` in the actual rational-point quotient by `f(C_A)`. -/
def CAplusQuotient :
    Submonoid (rationalPoints T.toGrp ⧸
      (CA F A).map (rationalPoints.map (CommGroupScheme.groupHom f))) :=
  (CAplusMonoid F T R).map
    (QuotientGroup.mk'
      ((CA F A).map (rationalPoints.map (CommGroupScheme.groupHom f))))

/-- Membership in the quotient image has an actual nonnegative section
representative. -/
theorem mem_CAplusQuotient
    (x : rationalPoints T.toGrp ⧸
      (CA F A).map (rationalPoints.map (CommGroupScheme.groupHom f))) :
    x ∈ CAplusQuotient F T R A f ↔
      ∃ a ∈ CAplus F T R,
        QuotientGroup.mk'
          ((CA F A).map (rationalPoints.map (CommGroupScheme.groupHom f))) a = x := by
  change (∃ a, a ∈ CAplusMonoid F T R ∧ _) ↔ _
  simp only [mem_CAplusMonoid]

end Langlands.GroupScheme.CocharacterUniformizer
