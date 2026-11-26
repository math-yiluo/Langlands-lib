import Langlands.Global.AdelicWeilPositivePoints
import Langlands.Global.AdelicWeilNormOneComparisonProof
import Langlands.Global.AdelicNormOneQuotientIso
import Langlands.Global.AdelicSplitCenterMeasure

/-! # Positive rational quotients under the adelic Weil comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal ENNReal

namespace Langlands.Global.AdelicWeilRestriction

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus

variable (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {G : GroupScheme (Spec (CommRingCat.of L))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {W : GroupScheme (Spec (CommRingCat.of K))}
  (w : W ≅ AffineWeil.groupScheme K L G)

/-- The actual full point comparison for a group isomorphic to the affine Weil restriction. -/
def ambientEquiv : AdelicGroupPoints K W ≃ₜ* AdelicGroupPoints L G :=
  (adelicPointsIso K w).trans (adelicPointsContinuousEquiv K L G)

@[simp]
theorem ambientEquiv_apply (x : AdelicGroupPoints K W) :
    ambientEquiv K L w x =
      adelicPointsEquiv K L G (AdelicGroupPoints.map K W _ w.hom x) := rfl

/-- The actual principal point comparison. -/
def principalEquiv : RationalGroupPoints K W ≃* RationalGroupPoints L G :=
  (((yonedaGrp.mapIso w).app (Opposite.op
    ((algSpec (CommRingCat.of K)).obj (Opposite.op (CommAlgCat.of K K))))).groupIsoToMulEquiv).trans
      (rationalPointsEquiv K L G)

@[simp]
theorem ambientEquiv_rational (x : RationalGroupPoints K W) :
    ambientEquiv K L w (rational K W x) = rational L G (principalEquiv K L w x) := by
  have hx : rational K _ (W.affinePointsTarget w.hom (CommAlgCat.of K K) x) =
      AdelicGroupPoints.map K W _ w.hom (rational K W x) :=
    DFunLike.congr_fun (rational_naturality K W w.hom) x
  rw [ambientEquiv_apply, ← hx, adelicPointsEquiv_rational]
  rfl

theorem map_rationalSubgroup_eq :
    (rationalSubgroup K W).map (ambientEquiv K L w).toMonoidHom = rationalSubgroup L G := by
  ext x
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨principalEquiv K L w q, (ambientEquiv_rational K L w q).symm⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨p, rfl⟩ := (principalEquiv K L w).surjective q
    exact ⟨rational K W p, ⟨p, rfl⟩, ambientEquiv_rational K L w p⟩

/-- The norm-one restriction of the full point comparison. -/
def normOneEquiv : normOneSubgroup K W ≃ₜ* normOneSubgroup L G :=
  (normOnePointsIso w).trans
    (normOnePointsEquiv K L G (normOneComparison K L G).1 (normOneComparison K L G).2.2)

@[simp]
theorem normOneEquiv_val (x : normOneSubgroup K W) :
    (normOneEquiv K L w x : AdelicGroupPoints L G) = ambientEquiv K L w x := rfl

@[simp]
theorem normOneEquiv_rational (x : RationalGroupPoints K W) :
    normOneEquiv K L w (rationalNormOne K W x) =
      rationalNormOne L G (principalEquiv K L w x) :=
  Subtype.ext (ambientEquiv_rational K L w x)

theorem normOneEquiv_mem_rational (x : normOneSubgroup K W) :
    normOneEquiv K L w x ∈ rationalNormOneSubgroup L G ↔ x ∈ rationalNormOneSubgroup K W := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨p, rfl⟩ := (principalEquiv K L w).surjective q
    exact ⟨p, (normOneEquiv K L w).injective ((normOneEquiv_rational K L w p).trans hq)⟩
  · rintro ⟨p, rfl⟩
    exact ⟨principalEquiv K L w p, (normOneEquiv_rational K L w p).symm⟩

variable [IsAffine W.X.left] [LocallyOfFiniteType W.X.hom]

/-- The canonical comparison on the discrete norm-one rational quotients. -/
def normOneQuotientEquiv :
    NormOneRationalQuotient K W ≃ᵐ NormOneRationalQuotient L G :=
  LeftCosetSpace.measurableEquivOfMulEquiv (normOneEquiv K L w) _ _
    (normOneEquiv_mem_rational K L w)

omit [IsAffine W.X.left] [LocallyOfFiniteType W.X.hom] in
@[simp]
theorem normOneQuotientEquiv_mk (x : normOneSubgroup K W) :
    normOneQuotientEquiv K L w (LeftCosetSpace.mk _ x) =
      LeftCosetSpace.mk _ (normOneEquiv K L w x) := rfl

/-- Ratio of the two chosen norm-one Haar measures under the Weil comparison. -/
def normOneHaarFactor : ℝ≥0 :=
  haarScalarFactor (Measure.map (normOneEquiv K L w) Measure.haar) Measure.haar

theorem normOneHaarFactor_pos : 0 < normOneHaarFactor K L w := by
  let b := normOneEquiv K L w
  let mK : Measure (normOneSubgroup K W) := Measure.haar
  let : (Measure.map b mK).IsHaarMeasure := b.isHaarMeasure_map mK
  exact haarScalarFactor_pos_of_isHaarMeasure _ _

theorem map_normOneHaar :
    Measure.map (normOneEquiv K L w) (Measure.haar : Measure (normOneSubgroup K W)) =
      (normOneHaarFactor K L w : ℝ≥0∞) • (Measure.haar : Measure (normOneSubgroup L G)) := by
  let b := normOneEquiv K L w
  let mK : Measure (normOneSubgroup K W) := Measure.haar
  let : (Measure.map b mK).IsHaarMeasure := b.isHaarMeasure_map mK
  let : (Measure.map b mK).Regular := Measure.Regular.map b.toHomeomorph
  exact isMulLeftInvariant_eq_smul_of_regular _ _

include w in
theorem normOneHaar_rightInvariant
    [(Measure.haar : Measure (normOneSubgroup K W)).IsMulRightInvariant] :
    (Measure.haar : Measure (normOneSubgroup L G)).IsMulRightInvariant := by
  let b := normOneEquiv K L w
  let mK : Measure (normOneSubgroup K W) := Measure.haar
  let mL : Measure (normOneSubgroup L G) := Measure.haar
  let c : ℝ≥0∞ := normOneHaarFactor K L w
  have hc : c ≠ 0 := ENNReal.coe_ne_zero.mpr (normOneHaarFactor_pos K L w).ne'
  have hct : c ≠ ∞ := ENNReal.coe_ne_top
  have hm : Measure.map b mK = c • mL := map_normOneHaar K L w
  have hinv : (Measure.map b mK).IsMulRightInvariant := by
    change (Measure.map b.toHomeomorph.toMeasurableEquiv mK).IsMulRightInvariant
    rw [← b.toHomeomorph.toMeasurableEquiv.comap_symm]
    exact IsMulRightInvariant.comap mK
      (f := b.symm.toMonoidHom) b.toHomeomorph.toMeasurableEquiv.symm.measurableEmbedding
  rw [hm] at hinv
  let := hinv
  have hν : c⁻¹ • (c • mL) = mL := by
    rw [smul_smul, ENNReal.inv_mul_cancel hc hct, one_smul]
  change mL.IsMulRightInvariant
  rw [← hν]
  infer_instance

theorem map_normOneQuotientHaar :
    Measure.map (normOneQuotientEquiv K L w) (normOneRationalQuotientHaarMeasure K W) =
      (normOneHaarFactor K L w : ℝ≥0∞) • normOneRationalQuotientHaarMeasure L G := by
  let b := normOneEquiv K L w
  let mK : Measure (normOneSubgroup K W) := Measure.haar
  let mL : Measure (normOneSubgroup L G) := Measure.haar
  let : (Measure.map b mK).IsHaarMeasure := b.isHaarMeasure_map mK
  have hh := LeftCosetSpace.measurePreserving_discreteQuotientMeasure b _ _
    (normOneEquiv_mem_rational K L w) (isDiscrete_rationalNormOneSubgroup K W)
    (isDiscrete_rationalNormOneSubgroup L G) mK (Measure.map b mK) ⟨b.continuous.measurable, rfl⟩
  refine hh.map_eq.trans ?_
  rw [show Measure.map b mK = (normOneHaarFactor K L w : ℝ≥0∞) • mL from map_normOneHaar K L w]
  exact LeftCosetSpace.quotientMeasure_smul (rationalNormOneSubgroup L G) mL
    (LeftCosetSpace.fundamentalDomain _ (isDiscrete_rationalNormOneSubgroup L G)) _

section Positive

variable {T : CommGroupScheme (Spec (CommRingCat.of K))} {i : T.toGrp ⟶ W}
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  {I : Type u} [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
  {T' : CommGroupScheme (Spec (CommRingCat.of L))} {j : T'.toGrp ⟶ G}
  (hj : Function.Injective (characterRestrict j)) [(characterRestrict j).range.FiniteIndex]
  {J : Type u} [Fintype J] (e' : T'.toGrp ≅ splitTorus (Spec (CommRingCat.of L)) J)

include hi e hj e' in
omit [IsAffine W.X.left] [LocallyOfFiniteType W.X.hom] in
/-- Inclusion of positive subgroups is equality because both give a complement to norm-one. -/
theorem map_imageSubgroup_eq_of_le
    (h : (imageSubgroup K T W i).map (ambientEquiv K L w).toMonoidHom ≤
      imageSubgroup L T' G j) :
    (imageSubgroup K T W i).map (ambientEquiv K L w).toMonoidHom =
      imageSubgroup L T' G j := by
  refine le_antisymm h ?_
  rintro _ ⟨a, ha, rfl⟩
  change positivePointMap L G T' j ⟨a, ha⟩ ∈ _
  obtain ⟨x, hx⟩ := (ambientEquiv K L w).surjective (positivePointMap L G T' j ⟨a, ha⟩)
  let p := positiveFactor K W T i hi I e x
  let n := normOneFactor K W T i hi I e x
  have hx' : ambientEquiv K L w (positivePointMap K W T i p) *
      (normOneEquiv K L w n : AdelicGroupPoints L G) = positivePointMap L G T' j ⟨a, ha⟩ := by
    rw [normOneEquiv_val, ← map_mul, positivePointMap_mul_normOneFactor, hx]
  have hp : ambientEquiv K L w (positivePointMap K W T i p) ∈
      (imageSubgroup K T W i).map (ambientEquiv K L w).toMonoidHom :=
    ⟨_, ⟨p.val, p.property, rfl⟩, rfl⟩
  obtain ⟨b, hb, hb'⟩ := h hp
  change positivePointMap L G T' j ⟨b, hb⟩ = _ at hb'
  rw [← hb'] at hx'
  have hab : (⟨b, hb⟩ : intrinsicSubgroup L T') = ⟨a, ha⟩ := by
    have heq := congrArg (positiveFactor L G T' j hj J e') hx'
    rw [positiveFactor_mul_normOne, positiveFactor_positivePointMap] at heq
    exact heq
  rwa [← hab, hb']

include hi e hj e' in
omit [IsAffine W.X.left] [LocallyOfFiniteType W.X.hom] in
/-- The full Weil equivalence maps the positive image onto that of any upper split component. -/
theorem map_imageSubgroup_eq (hc : IsCentral i) (hs : IsSplitComponent j) :
    (imageSubgroup K T W i).map (ambientEquiv K L w).toMonoidHom =
      imageSubgroup L T' G j := by
  apply map_imageSubgroup_eq_of_le K L w hi e hj e'
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  apply map_imageSubgroup_le K L G T (i ≫ w.hom) I e (hc.comp_iso w) hs
  refine ⟨_, ⟨a, ha, rfl⟩, ?_⟩
  exact congrArg (adelicPointsEquiv K L G) (map_comp_apply_of_hom (p := w.hom) i a)

variable (hpos : (imageSubgroup K T W i).map (ambientEquiv K L w).toMonoidHom =
  imageSubgroup L T' G j)

include hpos in
omit [IsAffine W.X.left] [LocallyOfFiniteType W.X.hom]
  [(characterRestrict i).range.FiniteIndex] [(characterRestrict j).range.FiniteIndex] in
theorem map_positiveRationalSubgroup_eq :
    (positiveRationalSubgroup K W T i).map (ambientEquiv K L w).toMonoidHom =
      positiveRationalSubgroup L G T' j := by
  unfold positiveRationalSubgroup
  rw [Subgroup.map_sup, hpos, map_rationalSubgroup_eq]

/-- The comparison on the actual positive rational quotients. -/
def positiveQuotientEquiv : PositiveRationalQuotient K W T i ≃ₜ
    PositiveRationalQuotient L G T' j :=
  LeftCosetSpace.congrHomeomorph _ _ (ambientEquiv K L w)
    (map_positiveRationalSubgroup_eq K L w hpos)

omit [IsAffine W.X.left] [LocallyOfFiniteType W.X.hom]
  [(characterRestrict i).range.FiniteIndex] [(characterRestrict j).range.FiniteIndex] in
@[simp]
theorem positiveQuotientEquiv_mk (x : AdelicGroupPoints K W) :
    positiveQuotientEquiv K L w hpos (LeftCosetSpace.mk _ x) =
      LeftCosetSpace.mk _ (ambientEquiv K L w x) := rfl

omit [IsAffine W.X.left] [LocallyOfFiniteType W.X.hom]
  [(characterRestrict i).range.FiniteIndex] [(characterRestrict j).range.FiniteIndex] in
theorem positiveQuotientEquiv_rightTranslate (x : AdelicGroupPoints K W)
    (q : PositiveRationalQuotient K W T i) :
    positiveQuotientEquiv K L w hpos (LeftCosetSpace.rightTranslate _ x q) =
      LeftCosetSpace.rightTranslate _ (ambientEquiv K L w x)
        (positiveQuotientEquiv K L w hpos q) := by
  induction q using Quotient.inductionOn with
  | _ y =>
      change LeftCosetSpace.mk _ (ambientEquiv K L w (y * x)) =
        LeftCosetSpace.mk _ (ambientEquiv K L w y * ambientEquiv K L w x)
      rw [map_mul]

include hi e hj e' in
theorem map_positiveQuotientHaar (hc : IsCentral i) (hc' : IsCentral j) :
    Measure.map (positiveQuotientEquiv K L w hpos)
        (positiveRationalQuotientHaarMeasure K W T i) =
      (normOneHaarFactor K L w : ℝ≥0∞) • positiveRationalQuotientHaarMeasure L G T' j := by
  let := positiveRationalQuotient_borelSpace K W T i hi I e hc
  let := positiveRationalQuotient_borelSpace L G T' j hj J e' hc'
  let q := positiveQuotientEquiv K L w hpos
  let qK := positiveQuotientMeasurableEquiv K W T i hi I e hc
  let qL := positiveQuotientMeasurableEquiv L G T' j hj J e' hc'
  let b := normOneQuotientEquiv K L w
  have hcomm : q ∘ qK = qL ∘ b := by
    funext x
    induction x using Quotient.inductionOn with
    | _ x => rfl
  change Measure.map q (Measure.map qK (normOneRationalQuotientHaarMeasure K W)) =
    _ • Measure.map qL (normOneRationalQuotientHaarMeasure L G)
  rw [Measure.map_map q.continuous.measurable qK.measurable, hcomm,
    ← Measure.map_map qL.measurable b.measurable,
    show Measure.map b _ = _ from map_normOneQuotientHaar K L w, Measure.map_smul]
  exact qL.measurable.aemeasurable

end Positive

end Langlands.Global.AdelicWeilRestriction
