import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndexProof
import Langlands.Global.AdelicNormOneHaarRightInvariantProof

/-! # The canonical restriction split-centre quotient `[G]`

Every affine group scheme locally of finite type over a field has a split component, namely its
largest central split torus. Choosing one split component of the Weil restriction
`Res_{F/ℚ} G` and one of `G` gives a quotient `[G] = A_G G(F) \ G(𝔸_F)` and a measure on it that
take no further data. Every other split component of the restriction gives the same subgroup,
and its quotient is identified with the chosen one by a measure-preserving homeomorphism that
intertwines right translation.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Existence

variable {k : Type u} [Field k]

/-- A closed subgroup can be cancelled on the right. -/
private theorem cancel_of_isClosedSubgroup {S : Scheme.{u}} {H G K : GroupScheme S}
    {i : H ⟶ G} (hi : IsClosedSubgroup i) {f g : K ⟶ H} (h : f ≫ i = g ≫ i) : f = g := by
  have : IsClosedImmersion i.hom.hom.left := hi
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  have h' := congrArg (fun q : K ⟶ G => q.hom.hom.left) h
  exact (cancel_mono i.hom.hom.left).mp h'

/-- Every affine group scheme locally of finite type over a field has a split component: its
largest central split torus. No reductivity is assumed. -/
theorem exists_isSplitComponent (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] :
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (i : A.toGrp ⟶ G), IsSplitComponent i := by
  obtain ⟨B, j, hj, huniv⟩ := exists_largestCentralSplitTorus G (finiteType_coordinateAlgebra G)
  refine ⟨B, j, hj, fun A' i' hi' f hf => ?_⟩
  obtain ⟨g, hg⟩ := huniv A' i' hi'.1.1 hi'.2
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply cancel_of_isClosedSubgroup hj.1.2
    rw [Category.assoc, hg, hf, Category.id_comp]
  · apply cancel_of_isClosedSubgroup hi'.1.2
    rw [Category.assoc, hf, hg, Category.id_comp]

end Existence

end Langlands.GroupScheme

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme Langlands.QuotientIntegration PositiveRealTorus
  Langlands.Automorphic.GroupSchemeFunctions

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

section Choice

/-- The source torus of the chosen split component of the Weil restriction `Res_{F/ℚ} G`. -/
def canonicalRestrictionTorus : CommGroupScheme (Spec (CommRingCat.of ℚ)) :=
  (exists_isSplitComponent (AffineWeil.groupScheme ℚ F G)).choose

/-- The chosen split component of the Weil restriction `Res_{F/ℚ} G`. -/
def canonicalRestrictionComponent :
    (canonicalRestrictionTorus F G).toGrp ⟶ AffineWeil.groupScheme ℚ F G :=
  (exists_isSplitComponent (AffineWeil.groupScheme ℚ F G)).choose_spec.choose

theorem isSplitComponent_canonicalRestrictionComponent :
    IsSplitComponent (canonicalRestrictionComponent F G) :=
  (exists_isSplitComponent (AffineWeil.groupScheme ℚ F G)).choose_spec.choose_spec

/-- The source torus of the chosen split component of `G`. -/
def canonicalTorus : CommGroupScheme (Spec (CommRingCat.of F)) :=
  (exists_isSplitComponent G).choose

/-- The chosen split component of `G`. -/
def canonicalComponent : (canonicalTorus F G).toGrp ⟶ G :=
  (exists_isSplitComponent G).choose_spec.choose

omit [NumberField F] in
theorem isSplitComponent_canonicalComponent : IsSplitComponent (canonicalComponent F G) :=
  (exists_isSplitComponent G).choose_spec.choose_spec

end Choice

local notation "S₀" => canonicalRestrictionTorus F G
local notation "j₀" => canonicalRestrictionComponent F G
local notation "T₀" => canonicalTorus F G
local notation "i₀" => canonicalComponent F G
local notation "hj₀" => isSplitComponent_canonicalRestrictionComponent F G
local notation "hs₀" => isSplitComponent_canonicalComponent F G

section Quotient

/-- The canonical split-centre subgroup `A_G` of `G(𝔸_F)`: the positive real points of the
chosen split component of `Res_{F/ℚ} G`. -/
abbrev canonicalSubgroup : Subgroup (AdelicGroupPoints F G) :=
  subgroup F G S₀ j₀

/-- The canonical subgroup together with the principal rational points. -/
abbrev canonicalRationalSubgroup : Subgroup (AdelicGroupPoints F G) :=
  rationalSubgroup F G S₀ j₀

/-- The canonical quotient `[G] = A_G G(F) \ G(𝔸_F)`. -/
abbrev CanonicalQuotient := Quotient F G S₀ j₀

/-- The canonical measure on `[G]`: the published restriction quotient measure. -/
abbrev canonicalMeasure : Measure (CanonicalQuotient F G) :=
  quotientHaarMeasure F G S₀ j₀

/-- The canonical subgroup is the positive image of the chosen split component of `G`. -/
theorem canonicalSubgroup_eq_imageSubgroup : canonicalSubgroup F G = imageSubgroup F T₀ G i₀ :=
  subgroup_eq_of_splitComponents F G hj₀ hs₀

variable {F G}

/-- Every split component of the restriction gives the canonical subgroup. -/
theorem subgroup_eq_canonicalSubgroup {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
    {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G} (hj : IsSplitComponent j) :
    subgroup F G S j = canonicalSubgroup F G :=
  (subgroup_eq_of_splitComponents F G hj hs₀).trans (canonicalSubgroup_eq_imageSubgroup F G).symm

/-- Every split component of `G` has the canonical subgroup as positive image. -/
theorem imageSubgroup_eq_canonicalSubgroup {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {i : T.toGrp ⟶ G} (hs : IsSplitComponent i) :
    imageSubgroup F T G i = canonicalSubgroup F G :=
  (subgroup_eq_of_splitComponents F G hj₀ hs).symm

theorem rationalSubgroup_eq_canonicalRationalSubgroup
    {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
    {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G} (hj : IsSplitComponent j) :
    rationalSubgroup F G S j = canonicalRationalSubgroup F G := by
  change subgroup F G S j ⊔ _ = canonicalSubgroup F G ⊔ _
  rw [subgroup_eq_canonicalSubgroup hj]

end Quotient

section Independence

variable {F G}
variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
  {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}

/-- The identity on representatives from the quotient of any split component of the
restriction to the canonical quotient. -/
def toCanonicalQuotient (hj : IsSplitComponent j) : Quotient F G S j ≃ₜ CanonicalQuotient F G :=
  LeftCosetSpace.congrSubgroupHomeomorph (rationalSubgroup_eq_canonicalRationalSubgroup hj)

@[simp] theorem toCanonicalQuotient_mk (hj : IsSplitComponent j) (x : AdelicGroupPoints F G) :
    toCanonicalQuotient hj (LeftCosetSpace.mk (rationalSubgroup F G S j) x) =
      LeftCosetSpace.mk (canonicalRationalSubgroup F G) x :=
  LeftCosetSpace.congrSubgroupHomeomorph_mk _ x

theorem toCanonicalQuotient_rightTranslate (hj : IsSplitComponent j) (g : AdelicGroupPoints F G)
    (q : Quotient F G S j) :
    toCanonicalQuotient hj (LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) g q) =
      LeftCosetSpace.rightTranslate (canonicalRationalSubgroup F G) g (toCanonicalQuotient hj q) :=
  LeftCosetSpace.congrSubgroupHomeomorph_rightTranslate _ g q

/-- The same identification as an equivalence of the inherited quotient sigma algebras. -/
def toCanonicalQuotientMeasurableEquiv (hj : IsSplitComponent j) :
    Quotient F G S j ≃ᵐ CanonicalQuotient F G where
  toEquiv := (toCanonicalQuotient hj).toEquiv
  measurable_toFun := LeftCosetSpace.measurable_congrSubgroupHomeomorph _
  measurable_invFun := LeftCosetSpace.measurable_congrSubgroupHomeomorph_symm _

@[simp] theorem coe_toCanonicalQuotientMeasurableEquiv (hj : IsSplitComponent j) :
    ⇑(toCanonicalQuotientMeasurableEquiv hj) = toCanonicalQuotient hj :=
  rfl

/-- The identification carries the quotient measure of any split component of the restriction
to the canonical measure. -/
theorem measurePreserving_toCanonicalQuotient (hj : IsSplitComponent j) :
    MeasurePreserving (toCanonicalQuotientMeasurableEquiv hj) (quotientHaarMeasure F G S j)
      (canonicalMeasure F G) := by
  refine ⟨(toCanonicalQuotientMeasurableEquiv hj).measurable, ?_⟩
  rw [quotientHaarMeasure, Measure.map_map (toCanonicalQuotientMeasurableEquiv hj).measurable
    (measurable_normOneToQuotient F G S j)]
  have hcomp : (toCanonicalQuotientMeasurableEquiv hj) ∘ normOneToQuotient F G S j =
      normOneToQuotient F G S₀ j₀ := by
    funext q
    induction q using Quotient.inductionOn with
    | _ n => exact toCanonicalQuotient_mk hj n.val
  rw [hcomp]
  rfl

/-- The identity on representatives from the positive-torus quotient of any split component of
`G` to the canonical quotient. -/
def positiveToCanonicalQuotient {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {i : T.toGrp ⟶ G} (hs : IsSplitComponent i) :
    PositiveRationalQuotient F G T i ≃ᵐ CanonicalQuotient F G :=
  quotientMeasurableEquiv F G (imageSubgroup_eq_canonicalSubgroup hs).symm

theorem measurePreserving_positiveToCanonicalQuotient
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
    (hs : IsSplitComponent i) :
    MeasurePreserving (positiveToCanonicalQuotient hs)
      (positiveRationalQuotientHaarMeasure F G T i) (canonicalMeasure F G) :=
  measurePreserving_quotientMeasurableEquiv F G _

end Independence

section Reductive

variable (hCST : CentralSplitTorusCharacterStatement.{0}) (hG : IsConnectedReductive G)

omit [NumberField F] in
include hCST hG in
/-- Assuming that central split tori detect nonzero rational characters, restriction of rational
characters to the chosen split component of a connected reductive `G` is injective. -/
theorem canonical_characterRestrict_injective :
    Function.Injective (characterRestrict (canonicalComponent F G)) :=
  characterRestrict_injective_of_centralSplitTorusCharacter hCST hG hs₀

omit [NumberField F] in
include hG in
/-- For connected reductive `G`, restriction of rational characters to the chosen split
component has finite-index range. -/
theorem canonical_finiteIndex : (characterRestrict (canonicalComponent F G)).range.FiniteIndex :=
  characterRestrictionFiniteIndexStatement F G hG _ _ hs₀

include hCST hG in
/-- The canonical combined subgroup `A_G G(F)` is closed in `G(𝔸_F)`. -/
theorem isClosed_canonicalRationalSubgroup :
    IsClosed (canonicalRationalSubgroup F G : Set (AdelicGroupPoints F G)) :=
  haveI := canonical_finiteIndex F G hG
  isClosed_rationalSubgroup F G (canonical_characterRestrict_injective F G hCST hG)
    (canonicalSubgroup_eq_imageSubgroup F G) hs₀.1.2 hs₀.1.1.1

include hCST hG in
theorem canonicalQuotient_t2Space : T2Space (CanonicalQuotient F G) :=
  haveI := canonical_finiteIndex F G hG
  quotient_t2Space F G (canonical_characterRestrict_injective F G hCST hG)
    (canonicalSubgroup_eq_imageSubgroup F G) hs₀.1.2 hs₀.1.1.1

include hCST hG in
/-- The inherited quotient sigma algebra on `[G]` is Borel. -/
theorem canonicalQuotient_borelSpace : BorelSpace (CanonicalQuotient F G) :=
  haveI := canonical_finiteIndex F G hG
  quotient_borelSpace F G (canonical_characterRestrict_injective F G hCST hG)
    (canonicalSubgroup_eq_imageSubgroup F G) hs₀.1.2 hs₀.1.1.1

/-- The full Haar measure on `A_G G(F)`, transported from the intrinsic positive-torus
normalization of the chosen split component of `G`. -/
def canonicalSubgroupHaarMeasure : Measure (canonicalRationalSubgroup F G) :=
  haveI := canonical_finiteIndex F G hG
  subgroupHaarMeasure F G (canonical_characterRestrict_injective F G hCST hG)
    (canonicalSubgroup_eq_imageSubgroup F G) hs₀.1.2 hs₀.1.1.1

instance canonicalSubgroupHaarMeasure_isMulRightInvariant :
    IsMulRightInvariant (canonicalSubgroupHaarMeasure F G hCST hG) :=
  haveI := canonical_finiteIndex F G hG
  subgroupHaarMeasure_isMulRightInvariant F G _ _ _ _

theorem canonicalSubgroupHaarMeasure_isHaarMeasure :
    (canonicalSubgroupHaarMeasure F G hCST hG).IsHaarMeasure :=
  haveI := canonical_finiteIndex F G hG
  subgroupHaarMeasure_isHaarMeasure F G _ _ _ _

/-- The canonical measure on `[G]` is Weil compatible with Haar measure on `G(𝔸_F)` and the
canonical Haar measure on `A_G G(F)`. -/
theorem canonicalMeasure_isCompatible :
    IsCompatible (canonicalRationalSubgroup F G) (Measure.haar : Measure (AdelicGroupPoints F G))
      (canonicalSubgroupHaarMeasure F G hCST hG) (canonicalMeasure F G) :=
  haveI := canonical_finiteIndex F G hG
  haveI := AdelicGroupPoints.normOneHaarRightInvariant F G hG.smooth hG.connectedSpace
  quotientHaarMeasure_isCompatible F G _ _ _ _

include hCST hG in
/-- The canonical measure on `[G]` is invariant under every right translation. -/
theorem canonicalMeasure_rightInvariant : QuotientRightInvariant F G (canonicalMeasure F G) :=
  haveI := canonical_finiteIndex F G hG
  haveI := AdelicGroupPoints.normOneHaarRightInvariant F G hG.smooth hG.connectedSpace
  quotientHaarMeasure_rightInvariant_of_splitComponents F G
    (canonical_characterRestrict_injective F G hCST hG) hj₀ hs₀

include hCST hG in
/-- The canonical measure on `[G]` is positive on nonempty open sets. -/
theorem canonicalMeasure_isOpenPosMeasure : (canonicalMeasure F G).IsOpenPosMeasure :=
  haveI := canonical_finiteIndex F G hG
  haveI := AdelicGroupPoints.normOneHaarRightInvariant F G hG.smooth hG.connectedSpace
  quotientHaarMeasure_isOpenPosMeasure_of_splitComponents F G
    (canonical_characterRestrict_injective F G hCST hG) hj₀ hs₀

end Reductive

section L2

/-- `L²` of the positive-torus quotient of the chosen split component of `G`, identified with
`L²([G])` for the canonical measure. -/
def canonicalL2Equiv :
    QuotientL2 F G T₀ i₀ (positiveRationalQuotientHaarMeasure F G T₀ i₀) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (canonicalMeasure F G) :=
  splitComponentL2Equiv F G hj₀ hs₀

variable (hCST : CentralSplitTorusCharacterStatement.{0}) (hG : IsConnectedReductive G)

/-- The right regular representation of `G(𝔸_F)` on `L²([G])` for the canonical measure. -/
def canonicalL2RightAction :
    Representation ℂ (AdelicGroupPoints F G) (Lp ℂ 2 (canonicalMeasure F G)) :=
  rationalQuotientL2RightAction F G _ (canonicalMeasure_rightInvariant F G hCST hG)

/-- The identification intertwines the published right regular representation on the
positive-torus quotient with the canonical right regular representation. -/
theorem canonicalL2Equiv_rightAction
    (hInv : QuotientMeasureRightInvariant F G T₀ i₀ (positiveRationalQuotientHaarMeasure F G T₀ i₀))
    (g : AdelicGroupPoints F G)
    (f : QuotientL2 F G T₀ i₀ (positiveRationalQuotientHaarMeasure F G T₀ i₀)) :
    canonicalL2Equiv F G (quotientL2RightAction F G T₀ i₀ _ hInv g f) =
      canonicalL2RightAction F G hCST hG g (canonicalL2Equiv F G f) :=
  quotientL2Equiv_rightAction F G _ hInv _ g f

variable {F G}
variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
  {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}

/-- Composition with the inverse identification, from canonical classes to the classes of any
split component of the restriction. -/
def fromCanonicalL2Map (hj : IsSplitComponent j) :
    Lp ℂ 2 (canonicalMeasure F G) →ₗᵢ[ℂ] Lp ℂ 2 (quotientHaarMeasure F G S j) :=
  Lp.compMeasurePreservingₗᵢ ℂ (toCanonicalQuotientMeasurableEquiv hj)
    (measurePreserving_toCanonicalQuotient hj)

/-- Composition with the identification, from the classes of any split component of the
restriction to canonical classes. -/
def toCanonicalL2Map (hj : IsSplitComponent j) :
    Lp ℂ 2 (quotientHaarMeasure F G S j) →ₗᵢ[ℂ] Lp ℂ 2 (canonicalMeasure F G) :=
  Lp.compMeasurePreservingₗᵢ ℂ (toCanonicalQuotientMeasurableEquiv hj).symm
    (MeasurePreserving.symm _ (measurePreserving_toCanonicalQuotient hj))

theorem fromCanonicalL2Map_toCanonicalL2Map (hj : IsSplitComponent j)
    (f : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    fromCanonicalL2Map hj (toCanonicalL2Map hj f) = f := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
  rw [← Lp.compMeasurePreserving_comp_apply,
    compMeasurePreserving_congr _ (MeasurePreserving.id _)
      (toCanonicalQuotientMeasurableEquiv hj).symm_comp_self]
  exact Lp.compMeasurePreserving_id_apply f

theorem toCanonicalL2Map_fromCanonicalL2Map (hj : IsSplitComponent j)
    (f : Lp ℂ 2 (canonicalMeasure F G)) :
    toCanonicalL2Map hj (fromCanonicalL2Map hj f) = f := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
  rw [← Lp.compMeasurePreserving_comp_apply,
    compMeasurePreserving_congr _ (MeasurePreserving.id _)
      (toCanonicalQuotientMeasurableEquiv hj).self_comp_symm]
  exact Lp.compMeasurePreserving_id_apply f

/-- `L²` of the quotient of any split component of the restriction, identified with canonical
`L²([G])` by composition with the identity on representatives. -/
def toCanonicalL2Equiv (hj : IsSplitComponent j) :
    Lp ℂ 2 (quotientHaarMeasure F G S j) ≃ₗᵢ[ℂ] Lp ℂ 2 (canonicalMeasure F G) :=
  LinearIsometryEquiv.ofLinearIsometry (toCanonicalL2Map hj) (fromCanonicalL2Map hj).toLinearMap
    (LinearMap.ext (toCanonicalL2Map_fromCanonicalL2Map hj))
    (LinearMap.ext (fromCanonicalL2Map_toCanonicalL2Map hj))

theorem coeFn_toCanonicalL2Equiv (hj : IsSplitComponent j)
    (f : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    toCanonicalL2Equiv hj f =ᵐ[canonicalMeasure F G]
      fun q => f ((toCanonicalQuotientMeasurableEquiv hj).symm q) :=
  Lp.coeFn_compMeasurePreserving f _

set_option maxRecDepth 20000 in
/-- The identification intertwines right regular representations for any right-invariance
proofs. -/
theorem toCanonicalL2Equiv_rightAction (hj : IsSplitComponent j)
    (hInv : QuotientRightInvariant F G (quotientHaarMeasure F G S j))
    (hInv' : QuotientRightInvariant F G (canonicalMeasure F G))
    (g : AdelicGroupPoints F G) (f : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    toCanonicalL2Equiv hj (rationalQuotientL2RightAction F G _ hInv g f) =
      rationalQuotientL2RightAction F G _ hInv' g (toCanonicalL2Equiv hj f) := by
  change Lp.compMeasurePreserving (toCanonicalQuotientMeasurableEquiv hj).symm
      (MeasurePreserving.symm _ (measurePreserving_toCanonicalQuotient hj))
      (Lp.compMeasurePreserving
        (LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) g) (hInv g) f) =
    Lp.compMeasurePreserving
      (LeftCosetSpace.rightTranslate (canonicalRationalSubgroup F G) g) (hInv' g)
      (Lp.compMeasurePreserving (toCanonicalQuotientMeasurableEquiv hj).symm
        (MeasurePreserving.symm _ (measurePreserving_toCanonicalQuotient hj)) f)
  rw [← Lp.compMeasurePreserving_comp_apply, ← Lp.compMeasurePreserving_comp_apply]
  apply compMeasurePreserving_congr
  funext q
  obtain ⟨p, rfl⟩ := (toCanonicalQuotientMeasurableEquiv hj).surjective q
  apply (toCanonicalQuotientMeasurableEquiv hj).injective
  simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply,
    MeasurableEquiv.apply_symm_apply]
  exact toCanonicalQuotient_rightTranslate hj g p

end L2

end Langlands.Global.RestrictionSplitCentre
