import Langlands.Automorphic.GroupSchemeQuotientL2
import Langlands.Global.AdelicRestrictionSplitCentreQuotient
import Langlands.Global.AdelicRestrictionSplitCentreComparison

/-! # Square-integrable classes on the restriction split-centre quotient -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
variable {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- Composition on `L²` depends only on the underlying measure-preserving map. -/
theorem compMeasurePreserving_congr {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μα : Measure α} {μβ : Measure β} {φ ψ : α → β} (hφ : MeasurePreserving φ μα μβ)
    (hψ : MeasurePreserving ψ μα μβ) (h : φ = ψ) (f : Lp ℂ 2 μβ) :
    Lp.compMeasurePreserving φ hφ f = Lp.compMeasurePreserving ψ hψ f := by
  subst h
  rfl

/-- Right invariance of a measure on the restriction quotient under every actual right
translation. -/
def QuotientRightInvariant (measureQ : Measure (Quotient F G S j)) : Prop :=
  ∀ g : AdelicGroupPoints F G,
    MeasurePreserving (LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) g)
      measureQ measureQ

/-- Composition with the inverse identification, from positive-torus to restriction classes. -/
def quotientL2Map (h : subgroup F G S j = imageSubgroup F T G i) :
    QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i) →ₗᵢ[ℂ]
      Lp ℂ 2 (quotientHaarMeasure F G S j) :=
  Lp.compMeasurePreservingₗᵢ ℂ (quotientMeasurableEquiv F G h).symm
    (MeasurePreserving.symm _ (measurePreserving_quotientMeasurableEquiv F G h))

/-- Composition with the identification, from restriction to positive-torus classes. -/
def quotientL2InvMap (h : subgroup F G S j = imageSubgroup F T G i) :
    Lp ℂ 2 (quotientHaarMeasure F G S j) →ₗᵢ[ℂ]
      QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i) :=
  Lp.compMeasurePreservingₗᵢ ℂ (quotientMeasurableEquiv F G h)
    (measurePreserving_quotientMeasurableEquiv F G h)

theorem quotientL2InvMap_quotientL2Map (h : subgroup F G S j = imageSubgroup F T G i)
    (f : QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i)) :
    quotientL2InvMap F G h (quotientL2Map F G h f) = f := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
  rw [← Lp.compMeasurePreserving_comp_apply,
    compMeasurePreserving_congr _ (MeasurePreserving.id _)
      (quotientMeasurableEquiv F G h).symm_comp_self]
  exact Lp.compMeasurePreserving_id_apply f

theorem quotientL2Map_quotientL2InvMap (h : subgroup F G S j = imageSubgroup F T G i)
    (f : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    quotientL2Map F G h (quotientL2InvMap F G h f) = f := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
  rw [← Lp.compMeasurePreserving_comp_apply,
    compMeasurePreserving_congr _ (MeasurePreserving.id _)
      (quotientMeasurableEquiv F G h).self_comp_symm]
  exact Lp.compMeasurePreserving_id_apply f

/-- Square-integrable classes for the positive-torus and restriction quotient measures,
identified by composition with the identity on representatives. -/
def quotientL2Equiv (h : subgroup F G S j = imageSubgroup F T G i) :
    QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (quotientHaarMeasure F G S j) :=
  LinearIsometryEquiv.ofLinearIsometry (quotientL2Map F G h)
    (quotientL2InvMap F G h).toLinearMap
    (LinearMap.ext (quotientL2Map_quotientL2InvMap F G h))
    (LinearMap.ext (quotientL2InvMap_quotientL2Map F G h))

theorem coeFn_quotientL2Equiv (h : subgroup F G S j = imageSubgroup F T G i)
    (f : QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i)) :
    quotientL2Equiv F G h f =ᵐ[quotientHaarMeasure F G S j]
      fun q => f ((quotientMeasurableEquiv F G h).symm q) :=
  Lp.coeFn_compMeasurePreserving f _

theorem coeFn_quotientL2Equiv_symm (h : subgroup F G S j = imageSubgroup F T G i)
    (f : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    (quotientL2Equiv F G h).symm f =ᵐ[positiveRationalQuotientHaarMeasure F G T i]
      fun q => f (quotientMeasurableEquiv F G h q) :=
  Lp.coeFn_compMeasurePreserving f _

/-- Right invariance of the positive-torus quotient measure gives right invariance of the
restriction quotient measure. -/
theorem quotientRightInvariant_of_positive (h : subgroup F G S j = imageSubgroup F T G i)
    (hInv : QuotientMeasureRightInvariant F G T i (positiveRationalQuotientHaarMeasure F G T i)) :
    QuotientRightInvariant F G (quotientHaarMeasure F G S j) := by
  intro g
  have hm := measurePreserving_quotientMeasurableEquiv F G h
  have hcomp : LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) g =
      (quotientMeasurableEquiv F G h) ∘
        LeftCosetSpace.rightTranslate (positiveRationalSubgroup F G T i) g ∘
          (quotientMeasurableEquiv F G h).symm := by
    funext q
    obtain ⟨p, rfl⟩ := (quotientMeasurableEquiv F G h).surjective q
    simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]
    exact (quotientHomeomorph_rightTranslate F G h g p).symm
  rw [hcomp]
  exact hm.comp ((hInv g).comp (MeasurePreserving.symm _ hm))

variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]

section Canonical

variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]

include hi in
/-- The restriction quotient measure is right invariant for split-torus data. -/
theorem quotientHaarMeasure_rightInvariant (h : subgroup F G S j = imageSubgroup F T G i)
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) :
    QuotientRightInvariant F G (quotientHaarMeasure F G S j) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  exact quotientRightInvariant_of_positive F G h
    (haarQuotientMeasureRightInvariant F G T i hi I e hc)

include hi in
/-- The restriction quotient measure is positive on nonempty open sets. -/
theorem quotientHaarMeasure_isOpenPosMeasure (h : subgroup F G S j = imageSubgroup F T G i)
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) :
    (quotientHaarMeasure F G S j).IsOpenPosMeasure := by
  let := quotient_borelSpace F G hi h hc hT
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  let : (AdelicGroupPoints.normOneRationalQuotientHaarMeasure F G).IsOpenPosMeasure :=
    (AdelicGroupPoints.normOneRationalQuotientHaarMeasure_isCompatible F G).isOpenPosMeasure
  have hmap : quotientHaarMeasure F G S j =
      (AdelicGroupPoints.normOneRationalQuotientHaarMeasure F G).map
        (normOneQuotientHomeomorph F G hi h I e hc) := by
    rw [coe_normOneQuotientHomeomorph]
    rfl
  rw [hmap]
  exact (normOneQuotientHomeomorph F G hi h I e hc).continuous.isOpenPosMeasure_map
    (normOneQuotientHomeomorph F G hi h I e hc).surjective

end Canonical

section Action

variable (measureQ : Measure (Quotient F G S j))
variable (hInv : QuotientRightInvariant F G measureQ)

/-- Right pullback is an isometry of `L²` on the restriction quotient. -/
def rationalQuotientL2RightTranslate (g : AdelicGroupPoints F G) :
    Lp ℂ 2 measureQ →ₗᵢ[ℂ] Lp ℂ 2 measureQ :=
  Lp.compMeasurePreservingₗᵢ ℂ (LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) g)
    (hInv g)

theorem coeFn_rationalQuotientL2RightTranslate (g : AdelicGroupPoints F G) (f : Lp ℂ 2 measureQ) :
    rationalQuotientL2RightTranslate F G measureQ hInv g f =ᵐ[measureQ]
      fun q => f (LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) g q) :=
  Lp.coeFn_compMeasurePreserving f (hInv g)

set_option maxRecDepth 20000 in
@[simp] theorem rationalQuotientL2RightTranslate_one (f : Lp ℂ 2 measureQ) :
    rationalQuotientL2RightTranslate F G measureQ hInv 1 f = f := by
  have hid : LeftCosetSpace.rightTranslate (rationalSubgroup F G S j)
      (1 : AdelicGroupPoints F G) = id :=
    funext (LeftCosetSpace.rightTranslate_one (rationalSubgroup F G S j))
  change Lp.compMeasurePreserving
    (LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) 1) (hInv 1) f = f
  simp only [hid]
  exact Lp.compMeasurePreserving_id_apply f

set_option maxRecDepth 20000 in
theorem rationalQuotientL2RightTranslate_mul (g g' : AdelicGroupPoints F G) (f : Lp ℂ 2 measureQ) :
    rationalQuotientL2RightTranslate F G measureQ hInv (g * g') f =
      rationalQuotientL2RightTranslate F G measureQ hInv g
        (rationalQuotientL2RightTranslate F G measureQ hInv g' f) := by
  have hcomp : LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) (g * g') =
      LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) g' ∘
        LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) g :=
    funext fun q => (LeftCosetSpace.rightTranslate_mul (rationalSubgroup F G S j) g g' q).symm
  change Lp.compMeasurePreserving
      (LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) (g * g')) (hInv (g * g')) f =
    Lp.compMeasurePreserving (LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) g) (hInv g)
      (Lp.compMeasurePreserving
        (LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) g') (hInv g') f)
  simpa only [← hcomp] using Lp.compMeasurePreserving_comp_apply f (hInv g') (hInv g)

/-- The right regular representation on `L²` of the restriction quotient. -/
def rationalQuotientL2RightAction :
    Representation ℂ (AdelicGroupPoints F G) (Lp ℂ 2 measureQ) where
  toFun g := (rationalQuotientL2RightTranslate F G measureQ hInv g).toLinearMap
  map_one' := by
    apply LinearMap.ext
    exact rationalQuotientL2RightTranslate_one F G measureQ hInv
  map_mul' g g' := by
    apply LinearMap.ext
    exact rationalQuotientL2RightTranslate_mul F G measureQ hInv g g'

end Action

omit [(characterRestrict i).range.FiniteIndex] in
set_option maxRecDepth 20000 in
/-- The `L²` identification intertwines the two right regular representations. -/
theorem quotientL2Equiv_rightAction (h : subgroup F G S j = imageSubgroup F T G i)
    (hInv : QuotientMeasureRightInvariant F G T i (positiveRationalQuotientHaarMeasure F G T i))
    (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))
    (g : AdelicGroupPoints F G)
    (f : QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i)) :
    quotientL2Equiv F G h (quotientL2RightAction F G T i _ hInv g f) =
      rationalQuotientL2RightAction F G _ hInv' g (quotientL2Equiv F G h f) := by
  change Lp.compMeasurePreserving (quotientMeasurableEquiv F G h).symm
      (MeasurePreserving.symm _ (measurePreserving_quotientMeasurableEquiv F G h))
      (Lp.compMeasurePreserving
        (LeftCosetSpace.rightTranslate (positiveRationalSubgroup F G T i) g) (hInv g) f) =
    Lp.compMeasurePreserving
      (LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) g) (hInv' g)
      (Lp.compMeasurePreserving (quotientMeasurableEquiv F G h).symm
        (MeasurePreserving.symm _ (measurePreserving_quotientMeasurableEquiv F G h)) f)
  rw [← Lp.compMeasurePreserving_comp_apply, ← Lp.compMeasurePreserving_comp_apply]
  apply compMeasurePreserving_congr
  funext q
  obtain ⟨p, rfl⟩ := (quotientMeasurableEquiv F G h).surjective q
  apply (quotientMeasurableEquiv F G h).injective
  simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply,
    MeasurableEquiv.apply_symm_apply]
  exact quotientHomeomorph_rightTranslate F G h g p

section SplitComponents

variable (hj : IsSplitComponent j) (hs : IsSplitComponent i)

omit [(characterRestrict i).range.FiniteIndex] in
include hj hs in
/-- For split components of the restriction and of `G`, the published comparison theorem gives
the subgroup equality. -/
theorem subgroup_eq_of_splitComponents : subgroup F G S j = imageSubgroup F T G i :=
  subgroup_eq_of_comparison F G comparison hj hs

omit [(characterRestrict i).range.FiniteIndex] in
/-- The `L²` identification for split components of the restriction and of `G`. -/
def splitComponentL2Equiv :
    QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (quotientHaarMeasure F G S j) :=
  quotientL2Equiv F G (subgroup_eq_of_splitComponents F G hj hs)

variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]

include hi hj hs in
/-- The restriction quotient measure is right invariant for split components. -/
theorem quotientHaarMeasure_rightInvariant_of_splitComponents :
    QuotientRightInvariant F G (quotientHaarMeasure F G S j) :=
  quotientHaarMeasure_rightInvariant F G hi (subgroup_eq_of_splitComponents F G hj hs)
    hs.1.2 hs.1.1.1

include hi hj hs in
/-- The restriction quotient measure is positive on nonempty open sets for split components. -/
theorem quotientHaarMeasure_isOpenPosMeasure_of_splitComponents :
    (quotientHaarMeasure F G S j).IsOpenPosMeasure :=
  quotientHaarMeasure_isOpenPosMeasure F G hi (subgroup_eq_of_splitComponents F G hj hs)
    hs.1.2 hs.1.1.1

/-- The right regular representation on `L²` of the restriction quotient for split
components. -/
def splitComponentL2RightAction :
    Representation ℂ (AdelicGroupPoints F G) (Lp ℂ 2 (quotientHaarMeasure F G S j)) :=
  rationalQuotientL2RightAction F G _
    (quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs)

/-- For split components, the `L²` identification intertwines the published right regular
representation on the positive-torus quotient with `splitComponentL2RightAction`. -/
theorem splitComponentL2Equiv_rightAction
    (hInv : QuotientMeasureRightInvariant F G T i (positiveRationalQuotientHaarMeasure F G T i))
    (g : AdelicGroupPoints F G)
    (f : QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i)) :
    splitComponentL2Equiv F G hj hs (quotientL2RightAction F G T i _ hInv g f) =
      splitComponentL2RightAction F G hi hj hs g (splitComponentL2Equiv F G hj hs f) :=
  quotientL2Equiv_rightAction F G _ hInv _ g f

end SplitComponents

end Langlands.Global.RestrictionSplitCentre
