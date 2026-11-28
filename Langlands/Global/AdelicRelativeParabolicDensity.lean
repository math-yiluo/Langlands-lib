import Langlands.Global.AdelicNormOneParabolicCoordinates

/-! # The parabolic Haar density in relative split coordinates -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Set Topology
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints.ParabolicIwasawaMeasure

open GroupScheme PositiveRealTorus

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P)
  [IsClosedImmersion (iU ≫ p).hom.hom.left] (l : M ⟶ P)
  [IsIso (subgroupMultiplication l iU)] (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
  (a : A.toGrp ⟶ M)

local notation "B" => relativePositiveSubgroup (l ≫ p) a
local notation "L" => ambientNormOneLevi (l ≫ p)
local notation "M₁" => normOneSubgroup F M

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  [IsClosedImmersion p.hom.hom.left] [IsClosedImmersion (iU ≫ p).hom.hom.left]
  [IsIso (subgroupMultiplication l iU)] in
/-- The inverse modulus is trivial on the intrinsic norm-one factor of the Levi. -/
theorem inverseModulus_mul_normOneLevi (m : AdelicGroupPoints F M) (m₁ : M₁) :
    inverseModulus l (m * m₁.val) = inverseModulus l m := by
  simp only [inverseModulus, InducedInnerProductIntegrable.parameterPower_map_mul_right
    _ l m₁.property]

/-- The inverse modulus as a density on the ambient norm-one positive split factor. -/
def relativePositiveDensity (x : B) : ℝ≥0∞ :=
  ENNReal.ofReal (inverseModulus l (positivePointMap F M A a x.val))

variable [IsAffineHom M.X.hom] (hM : IsConnectedReductive M) (ha : IsSplitComponent a)

/-- In split and intrinsic norm-one coordinates the parabolic density depends only on
the relative positive factor. -/
theorem normOneParabolicDensity_relativeLeviDecomposition
    (hG : IsConnectedReductive G) {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
    (hP : (Dynamic.parabolic χ).IsRepresentedBy p)
    (hN : (Dynamic.unipotent χ).IsRepresentedBy (iU ≫ p)) (x : B × M₁) :
    normOneParabolicDensity p iU l hU (relativeLeviDecomposition (l ≫ p) a hM ha x) =
      relativePositiveDensity p l a x.1 := by
  rw [normOneParabolicDensity_eq_inverseModulus p iU l hU hG hP hN,
    relativeLeviDecomposition_apply, inverseModulus_mul_normOneLevi]
  rfl

private theorem measurePreserving_withDensity_comp {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {f : X → Y} {dx : Measure X} {dy : Measure Y}
    (hf : MeasurePreserving f dx dy) {δ : Y → ℝ≥0∞} (hδ : Measurable δ) :
    MeasurePreserving f (dx.withDensity (δ ∘ f)) (dy.withDensity δ) := by
  refine ⟨hf.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
    withDensity_apply _ hs]
  exact hf.setLIntegral_comp_preimage hs hδ

/-- Fix a split Haar normalization before choosing any intrinsic norm-one Levi restriction.
The weight is entirely in the split coordinate and the intrinsic Haar factor is prescribed. -/
def RelativeParabolicDensityStatement (dm : Measure L) : Prop :=
  ∃ μA : Measure B, μA.IsHaarMeasure ∧ SigmaFinite μA ∧
    ∀ D : Set M₁,
      MeasurePreserving (relativeLeviDecomposition (l ≫ p) a hM ha)
        ((μA.withDensity (relativePositiveDensity p l a)).prod ((Measure.haar : Measure M₁).restrict D))
        ((dm.withDensity (normOneParabolicDensity p iU l hU)).restrict
          (relativeLeviDecomposition (l ≫ p) a hM ha '' (Set.univ ×ˢ D)))

/-- Transport the weighted Haar product through the Levi isomorphism and then restrict. -/
theorem relativeParabolicDensity
    (hG : IsConnectedReductive G) {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
    (hP : (Dynamic.parabolic χ).IsRepresentedBy p)
    (hN : (Dynamic.unipotent χ).IsRepresentedBy (iU ≫ p))
    (dm : Measure L) [dm.IsHaarMeasure] :
    RelativeParabolicDensityStatement p iU l hU a hM ha dm := by
  obtain ⟨μA, hμA, hsf, hE⟩ := exists_relativeLeviHaarProduct (l ≫ p) a hM ha dm
  let E := relativeLeviDecomposition (l ≫ p) a hM ha
  let w := normOneParabolicDensity p iU l hU
  let d := relativePositiveDensity p l a
  have hw : Measurable w := by
    have he : w = fun m => ENNReal.ofReal (inverseModulus l m.val) :=
      funext fun m => normOneParabolicDensity_eq_inverseModulus p iU l hU hG hP hN m
    rw [he]
    exact ENNReal.measurable_ofReal.comp ((continuous_inverseModulus l).measurable.comp measurable_subtype_coe)
  have hd : Measurable d :=
    ENNReal.measurable_ofReal.comp ((continuous_inverseModulus l).measurable.comp
      ((positivePointMap F M A a).continuous.measurable.comp measurable_subtype_coe))
  have heq : w ∘ E = fun x => d x.1 :=
    funext (normOneParabolicDensity_relativeLeviDecomposition p iU l hU a hM ha hG hP hN)
  have hweight : MeasurePreserving E ((μA.withDensity d).prod (Measure.haar : Measure M₁))
      (dm.withDensity w) := by
    rw [prod_withDensity_left hd, ← heq]
    exact measurePreserving_withDensity_comp hE hw
  refine ⟨μA, hμA, hsf, fun D => ?_⟩
  have hr := hweight.restrict_image_emb E.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (Set.univ ×ˢ D)
  rwa [← Measure.prod_restrict, Measure.restrict_univ] at hr

end Langlands.Global.AdelicGroupPoints.ParabolicIwasawaMeasure
