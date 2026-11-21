import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Global.AdelicIwasawaHeight
import Langlands.Global.DiscreteLeftCosetMeasureTransport

/-! # Transport of the actual norm-one Haar quotient by a scheme isomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal ENNReal

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme LeftCosetSpace

variable {F : Type u} [Field F] [NumberField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}

/-- The inverse group-scheme maps restrict to continuous inverse maps of the
actual norm-one groups. -/
def normOnePointsIso (e : G ≅ H) : normOneSubgroup F G ≃ₜ* normOneSubgroup F H where
  toFun := mapNormOne F G H e.hom
  invFun := mapNormOne F H G e.inv
  left_inv x := by
    apply Subtype.ext
    change map F H G e.inv (map F G H e.hom x.val) = x.val
    rw [← map_comp_apply_of_hom, e.hom_inv_id]
    change x.val ≫ 𝟙 G.X = x.val
    exact Category.comp_id _
  right_inv x := by
    apply Subtype.ext
    change map F G H e.hom (map F H G e.inv x.val) = x.val
    rw [← map_comp_apply_of_hom, e.inv_hom_id]
    change x.val ≫ 𝟙 H.X = x.val
    exact Category.comp_id _
  map_mul' := map_mul (mapNormOne F G H e.hom)
  continuous_toFun := (mapNormOne F G H e.hom).continuous
  continuous_invFun := (mapNormOne F H G e.inv).continuous

theorem normOnePointsIso_rational (e : G ≅ H) (x : normOneSubgroup F G) :
    normOnePointsIso e x ∈ rationalNormOneSubgroup F H ↔ x ∈ rationalNormOneSubgroup F G := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨H.affinePointsTarget e.inv (CommAlgCat.of F F) y, ?_⟩
    rw [← mapNormOne_rationalNormOne, hy]
    exact (normOnePointsIso e).symm_apply_apply x
  · rintro ⟨y, rfl⟩
    exact ⟨G.affinePointsTarget e.hom (CommAlgCat.of F F) y, (mapNormOne_rationalNormOne F G H e.hom y).symm⟩

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

/-- The actual quotient equivalence induced by the scheme isomorphism on the
norm-one groups and their principal lattices. -/
def normOneQuotientIso (e : G ≅ H) :
    NormOneRationalQuotient F G ≃ᵐ NormOneRationalQuotient F H :=
  measurableEquivOfMulEquiv (normOnePointsIso e) (rationalNormOneSubgroup F G)
    (rationalNormOneSubgroup F H) (normOnePointsIso_rational e)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] in
@[simp]
theorem normOneQuotientIso_mk (e : G ≅ H) (x : normOneSubgroup F G) :
    normOneQuotientIso e (LeftCosetSpace.mk (rationalNormOneSubgroup F G) x) =
      LeftCosetSpace.mk (rationalNormOneSubgroup F H) (normOnePointsIso e x) := rfl

/-- The two chosen norm-one quotient Haar measures differ under the actual
isomorphism by a positive constant. -/
def NormOneQuotientIsoHaarStatement (e : G ≅ H) : Prop :=
  ∃ s : ℝ≥0, 0 < s ∧
    Measure.map (normOneQuotientIso e) (normOneRationalQuotientHaarMeasure F G) =
      (s : ℝ≥0∞) • normOneRationalQuotientHaarMeasure F H

theorem normOneQuotientIsoHaar (e : G ≅ H) : NormOneQuotientIsoHaarStatement e := by
  let u := normOnePointsIso e
  let hG := isDiscrete_rationalNormOneSubgroup F G
  let hH := isDiscrete_rationalNormOneSubgroup F H
  let mG : Measure (normOneSubgroup F G) := Measure.haar
  let mH : Measure (normOneSubgroup F H) := Measure.haar
  let m := Measure.map u mG
  let : m.IsHaarMeasure := u.isHaarMeasure_map mG
  let : m.Regular := Measure.Regular.map u.toHomeomorph
  let s := haarScalarFactor m mH
  have hscalar : m = s • mH := isMulLeftInvariant_eq_smul_of_regular m mH
  have hmap := measurePreserving_discreteQuotientMeasure u
    (rationalNormOneSubgroup F G) (rationalNormOneSubgroup F H)
    (normOnePointsIso_rational e) hG hH mG m ⟨u.continuous.measurable, rfl⟩
  refine ⟨s, haarScalarFactor_pos_of_isHaarMeasure _ _, hmap.map_eq.trans ?_⟩
  rw [hscalar]
  exact quotientMeasure_smul (rationalNormOneSubgroup F H) mH
    (fundamentalDomain (rationalNormOneSubgroup F H) hH) (s : ℝ≥0∞)

end Langlands.Global.AdelicGroupPoints
