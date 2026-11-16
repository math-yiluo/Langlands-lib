import Langlands.GroupScheme.AffineGmAttractingScheme
import Langlands.GroupScheme.Dynamic.Uniqueness

/-! # The limit map from the attracting scheme to the fixed scheme -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace PointwiseSchemeAction

variable {S : Scheme.{u}} {X : Over S} (s : PointwiseSchemeAction (Gm S).toGrp X)

/-- A fixed point has a constant affine-line orbit extension. -/
theorem IsFixed.isAttracted {T : Over S} {x : T ⟶ X} (hx : s.IsFixed x) :
    s.IsAttracted x := by
  refine ⟨fst T (AffineLine.scheme S) ≫ x, ?_⟩
  rw [whiskerLeft_fst_assoc]
  exact ((s.isFixed_iff_universal x).mp hx).symm

variable [IsSeparated X.hom]

/-- An affine-line orbit extension into a separated target is unique. -/
theorem orbitExtension_unique {T : Over S} {x : T ⟶ X}
    {E E' : T ⊗ AffineLine.scheme S ⟶ X}
    (hE : T ◁ AffineLine.unitInclusion S ≫ E = s.orbit x)
    (hE' : T ◁ AffineLine.unitInclusion S ≫ E' = s.orbit x) : E = E' :=
  AffineLine.hom_ext_of_unitInclusion (hE.trans hE'.symm)

/-- Scaling the affine-line parameter agrees with the action on an orbit extension. -/
theorem orbitExtension_scale {T : Over S} {x : T ⟶ X}
    {E : T ⊗ AffineLine.scheme S ⟶ X}
    (hE : T ◁ AffineLine.unitInclusion S ≫ E = s.orbit x) :
    AffineLine.scale T ≫ E =
      s.act (fst _ _ ≫ snd _ _)
        (fst T (Gm S).X ▷ AffineLine.scheme S ≫ E) := by
  apply AffineLine.hom_ext_of_unitInclusion
  rw [AffineLine.whiskerLeft_unitInclusion_scale_assoc, hE, s.naturality,
    whisker_exchange_assoc, hE, s.whiskerRight_orbit]
  simp only [orbit, s.naturality, s.act_mul_left, whiskerLeft_fst_assoc,
    lift_fst_assoc, lift_snd, Category.assoc]

/-- Evaluating an orbit extension at zero gives an all-refinement fixed point. -/
theorem evalZero_isFixed {T : Over S} {x : T ⟶ X}
    {E : T ⊗ AffineLine.scheme S ⟶ X}
    (hE : T ◁ AffineLine.unitInclusion S ≫ E = s.orbit x) :
    s.IsFixed (Dynamic.evalZero E) := by
  rw [s.isFixed_iff_universal]
  have h := congrArg Dynamic.evalZero (s.orbitExtension_scale hE)
  change Dynamic.evalZero (AffineLine.scale T ≫ E) =
    Dynamic.evalZero (s.act _ _) at h
  rw [Dynamic.evalZero, ← Category.assoc, AffineLine.lift_zeroSection_scale,
    Category.assoc] at h
  rw [Dynamic.evalZero, s.naturality] at h
  simp only [lift_fst_assoc] at h
  simp only [Category.id_comp] at h
  change fst T (Gm S).X ≫ Dynamic.evalZero E =
    s.act (snd T (Gm S).X)
      (Dynamic.evalZero (fst T (Gm S).X ▷ AffineLine.scheme S ≫ E)) at h
  rw [Dynamic.evalZero_whiskerRight] at h
  exact h.symm

/-- A fixed point is the zero value of any extension of its orbit. -/
theorem evalZero_eq_of_isFixed {T : Over S} {x : T ⟶ X} (hx : s.IsFixed x)
    {E : T ⊗ AffineLine.scheme S ⟶ X}
    (hE : T ◁ AffineLine.unitInclusion S ≫ E = s.orbit x) :
    Dynamic.evalZero E = x := by
  have he : E = fst T (AffineLine.scheme S) ≫ x := by
    apply s.orbitExtension_unique hE
    rw [whiskerLeft_fst_assoc]
    exact ((s.isFixed_iff_universal x).mp hx).symm
  rw [he, Dynamic.evalZero_fst]

end PointwiseSchemeAction

namespace GmCoordinateAction

variable {R : CommRingCat.{u}} {X : Over (Spec R)} [IsAffine X.left]
  (s : PointwiseSchemeAction (Gm (Spec R)).toGrp X)

/-- Evaluation at zero of the universal attracting extension. -/
def schemeActionAttractingZero : schemeActionAttractingScheme s ⟶ X :=
  Dynamic.evalZero (schemeActionAttractingExtension s)

/-- The zero value is fixed on every relative refinement. -/
theorem schemeActionAttractingZero_isFixed :
    s.IsFixed (schemeActionAttractingZero s) :=
  s.evalZero_isFixed (schemeActionAttractingExtension_restrict s)

/-- The actual limit morphism to the fixed scheme. -/
def schemeActionAttractingLimit :
    schemeActionAttractingScheme s ⟶ schemeActionFixedScheme s :=
  ((exists_schemeActionFixed_factor_iff_all s (schemeActionAttractingZero s)).mpr
    (schemeActionAttractingZero_isFixed s)).choose

/-- Composing the limit map with the fixed inclusion evaluates the extension at zero. -/
theorem schemeActionAttractingLimit_comp :
    schemeActionAttractingLimit s ≫ schemeActionFixedHom s =
      schemeActionAttractingZero s :=
  ((exists_schemeActionFixed_factor_iff_all s (schemeActionAttractingZero s)).mpr
    (schemeActionAttractingZero_isFixed s)).choose_spec

/-- Restricting the universal extension to a factor gives any extension of that point. -/
theorem schemeActionAttractingExtension_naturality
    {T : Over (Spec R)} {x : T ⟶ X}
    (y : T ⟶ schemeActionAttractingScheme s)
    (hy : y ≫ schemeActionAttractingHom s = x)
    {E : T ⊗ AffineLine.scheme (Spec R) ⟶ X}
    (hE : T ◁ AffineLine.unitInclusion (Spec R) ≫ E = s.orbit x) :
    y ▷ AffineLine.scheme (Spec R) ≫ schemeActionAttractingExtension s = E := by
  apply s.orbitExtension_unique _ hE
  rw [whisker_exchange_assoc, schemeActionAttractingExtension_restrict,
    s.whiskerRight_orbit, hy]

/-- The limit of a factor is the zero value of any orbit extension of the point. -/
theorem schemeActionAttractingZero_naturality
    {T : Over (Spec R)} {x : T ⟶ X}
    (y : T ⟶ schemeActionAttractingScheme s)
    (hy : y ≫ schemeActionAttractingHom s = x)
    {E : T ⊗ AffineLine.scheme (Spec R) ⟶ X}
    (hE : T ◁ AffineLine.unitInclusion (Spec R) ≫ E = s.orbit x) :
    y ≫ schemeActionAttractingZero s = Dynamic.evalZero E := by
  rw [schemeActionAttractingZero, ← Dynamic.evalZero_whiskerRight,
    schemeActionAttractingExtension_naturality s y hy hE]

/-- The fixed scheme includes into the attracting scheme by constant orbits. -/
def schemeActionFixedToAttracting :
    schemeActionFixedScheme s ⟶ schemeActionAttractingScheme s :=
  ((exists_schemeActionAttracting_factor_iff_all s (schemeActionFixedHom s)).mpr
    (PointwiseSchemeAction.IsFixed.isAttracted s
      (schemeActionFixedHom_isFixed s))).choose

/-- The section is the same actual closed inclusion into X. -/
theorem schemeActionFixedToAttracting_comp :
    schemeActionFixedToAttracting s ≫ schemeActionAttractingHom s =
      schemeActionFixedHom s :=
  ((exists_schemeActionAttracting_factor_iff_all s (schemeActionFixedHom s)).mpr
    (PointwiseSchemeAction.IsFixed.isAttracted s
      (schemeActionFixedHom_isFixed s))).choose_spec

/-- The zero value of the fixed section is its original fixed point. -/
theorem schemeActionFixedToAttracting_comp_zero :
    schemeActionFixedToAttracting s ≫ schemeActionAttractingZero s =
      schemeActionFixedHom s := by
  have hE : schemeActionFixedScheme s ◁ AffineLine.unitInclusion (Spec R) ≫
      (fst (schemeActionFixedScheme s) (AffineLine.scheme (Spec R)) ≫
        schemeActionFixedHom s) = s.orbit (schemeActionFixedHom s) := by
    rw [whiskerLeft_fst_assoc]
    exact ((s.isFixed_iff_universal _).mp (schemeActionFixedHom_isFixed s)).symm
  rw [schemeActionAttractingZero_naturality s (schemeActionFixedToAttracting s)
    (schemeActionFixedToAttracting_comp s) hE, Dynamic.evalZero_fst]

/-- The fixed inclusion is a section of the actual limit map. -/
theorem schemeActionFixedToAttracting_comp_limit :
    schemeActionFixedToAttracting s ≫ schemeActionAttractingLimit s =
      𝟙 (schemeActionFixedScheme s) := by
  apply (cancel_mono (schemeActionFixedHom s)).mp
  rw [Category.assoc, schemeActionAttractingLimit_comp,
    schemeActionFixedToAttracting_comp_zero, Category.id_comp]

end GmCoordinateAction

end Langlands.GroupScheme
