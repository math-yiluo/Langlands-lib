import Langlands.Global.AdelicRestrictionSplitCentreComparisonStatement
import Langlands.Global.AdelicSplitComponentWeil

/-! # Measures and Weil compatibility on the restriction split-centre quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global

namespace LeftCosetSpace

open Langlands.QuotientIntegration

variable {H : Type u} [Group H] {Γ Δ : Subgroup H}

/-- The identity comparison of equal subgroups preserves right invariance of a measure. -/
theorem isMulRightInvariant_map_subgroupCongr [MeasurableSpace H] (h : Γ = Δ)
    (μΓ : Measure Γ) [IsMulRightInvariant μΓ] :
    IsMulRightInvariant (μΓ.map (MulEquiv.subgroupCongr h)) := by
  subst Δ
  have hid : ⇑(MulEquiv.subgroupCongr (rfl : Γ = Γ)) = id := rfl
  rw [hid, Measure.map_id]
  infer_instance

/-- The identity comparison of equal subgroups preserves Haar measures. -/
theorem isHaarMeasure_map_subgroupCongr [TopologicalSpace H] [MeasurableSpace H] (h : Γ = Δ)
    (μΓ : Measure Γ) [μΓ.IsHaarMeasure] :
    (μΓ.map (MulEquiv.subgroupCongr h)).IsHaarMeasure := by
  subst Δ
  have hid : ⇑(MulEquiv.subgroupCongr (rfl : Γ = Γ)) = id := rfl
  rw [hid, Measure.map_id]
  infer_instance

/-- Weil compatibility is unchanged when equal subgroups are identified, with the subgroup and
quotient measures moved by the identity comparisons. -/
theorem isCompatible_congrSubgroup [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (h : Γ = Δ) (μH : Measure H)
    (μΓ : Measure Γ) [IsMulRightInvariant μΓ] (μΔ : Measure Δ) [IsMulRightInvariant μΔ]
    (ν : Measure (LeftCosetSpace Γ)) (ν' : Measure (LeftCosetSpace Δ))
    (hμ : μΓ.map (MulEquiv.subgroupCongr h) = μΔ)
    (hν : ν.map (congrSubgroupHomeomorph h) = ν')
    (hc : IsCompatible Γ μH μΓ ν) : IsCompatible Δ μH μΔ ν' := by
  subst Δ
  have hμid : ⇑(MulEquiv.subgroupCongr (rfl : Γ = Γ)) = id := rfl
  have hνid : ⇑(congrSubgroupHomeomorph (rfl : Γ = Γ)) = id := rfl
  rw [hμid, Measure.map_id] at hμ
  rw [hνid, Measure.map_id] at hν
  subst μΔ ν'
  exact hc

end LeftCosetSpace

namespace RestrictionSplitCentre

open Langlands.GroupScheme Langlands.QuotientIntegration PositiveRealTorus

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
variable (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G)

/-- Inclusion of actual norm-one representatives descends to the restriction quotient. -/
def normOneToQuotient : AdelicGroupPoints.NormOneRationalQuotient F G → Quotient F G S j :=
  LeftCosetSpace.lift (AdelicGroupPoints.rationalNormOneSubgroup F G)
    (fun n => LeftCosetSpace.mk (rationalSubgroup F G S j)
      (n : AdelicGroupPoints F G)) (by
        intro q n
        exact LeftCosetSpace.mk_subgroup_mul (rationalSubgroup F G S j)
          ⟨q.val.val, principal_le_rationalSubgroup F G S j
            (AdelicGroupPoints.rationalNormOneSubgroupInclusion F G q).property⟩ n.val)

@[simp] theorem normOneToQuotient_mk (n : AdelicGroupPoints.normOneSubgroup F G) :
    normOneToQuotient F G S j
      (LeftCosetSpace.mk (AdelicGroupPoints.rationalNormOneSubgroup F G) n) =
        LeftCosetSpace.mk (rationalSubgroup F G S j) (n : AdelicGroupPoints F G) :=
  rfl

theorem measurable_normOneToQuotient : Measurable (normOneToQuotient F G S j) :=
  measurable_from_quotient.mpr
    ((LeftCosetSpace.measurable_mk (rationalSubgroup F G S j)).comp measurable_subtype_coe)

/-- Push the exact existing norm-one quotient Haar measure through actual inclusion. -/
def quotientHaarMeasure : Measure (Quotient F G S j) :=
  Measure.map (normOneToQuotient F G S j)
    (AdelicGroupPoints.normOneRationalQuotientHaarMeasure F G)

variable {S j}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}

/-- Equal positive images give equal subgroups after adjoining the principal points. -/
theorem rationalSubgroup_eq (h : subgroup F G S j = imageSubgroup F T G i) :
    rationalSubgroup F G S j = positiveRationalSubgroup F G T i := by
  unfold rationalSubgroup positiveRationalSubgroup
  rw [h]

/-- The identity on representatives from the positive-torus quotient. -/
def quotientHomeomorph (h : subgroup F G S j = imageSubgroup F T G i) :
    PositiveRationalQuotient F G T i ≃ₜ Quotient F G S j :=
  LeftCosetSpace.congrSubgroupHomeomorph (rationalSubgroup_eq F G h).symm

@[simp] theorem quotientHomeomorph_mk (h : subgroup F G S j = imageSubgroup F T G i)
    (x : AdelicGroupPoints F G) :
    quotientHomeomorph F G h (LeftCosetSpace.mk (positiveRationalSubgroup F G T i) x) =
      LeftCosetSpace.mk (rationalSubgroup F G S j) x :=
  LeftCosetSpace.congrSubgroupHomeomorph_mk _ x

theorem quotientHomeomorph_rightTranslate (h : subgroup F G S j = imageSubgroup F T G i)
    (g : AdelicGroupPoints F G) (q : PositiveRationalQuotient F G T i) :
    quotientHomeomorph F G h
      (LeftCosetSpace.rightTranslate (positiveRationalSubgroup F G T i) g q) =
        LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) g
          (quotientHomeomorph F G h q) :=
  LeftCosetSpace.congrSubgroupHomeomorph_rightTranslate _ g q

/-- The same identification as an equivalence of the inherited quotient sigma algebras. -/
def quotientMeasurableEquiv (h : subgroup F G S j = imageSubgroup F T G i) :
    PositiveRationalQuotient F G T i ≃ᵐ Quotient F G S j where
  toEquiv := (quotientHomeomorph F G h).toEquiv
  measurable_toFun := LeftCosetSpace.measurable_congrSubgroupHomeomorph _
  measurable_invFun := LeftCosetSpace.measurable_congrSubgroupHomeomorph_symm _

@[simp] theorem quotientMeasurableEquiv_mk (h : subgroup F G S j = imageSubgroup F T G i)
    (x : AdelicGroupPoints F G) :
    quotientMeasurableEquiv F G h (LeftCosetSpace.mk (positiveRationalSubgroup F G T i) x) =
      LeftCosetSpace.mk (rationalSubgroup F G S j) x :=
  quotientHomeomorph_mk F G h x

@[simp] theorem quotientMeasurableEquiv_normOneToPositiveQuotient
    (h : subgroup F G S j = imageSubgroup F T G i)
    (q : AdelicGroupPoints.NormOneRationalQuotient F G) :
    quotientMeasurableEquiv F G h (normOneToPositiveQuotient F G T i q) =
      normOneToQuotient F G S j q := by
  induction q using Quotient.inductionOn with
  | _ n => exact quotientMeasurableEquiv_mk F G h n.val

/-- The identification carries the positive-torus quotient measure to the quotient measure. -/
theorem measurePreserving_quotientMeasurableEquiv
    (h : subgroup F G S j = imageSubgroup F T G i) :
    MeasurePreserving (quotientMeasurableEquiv F G h)
      (positiveRationalQuotientHaarMeasure F G T i) (quotientHaarMeasure F G S j) := by
  refine ⟨(quotientMeasurableEquiv F G h).measurable, ?_⟩
  rw [positiveRationalQuotientHaarMeasure, Measure.map_map]
  · have hcomp : (quotientMeasurableEquiv F G h) ∘ normOneToPositiveQuotient F G T i =
        normOneToQuotient F G S j := by
      funext q
      exact quotientMeasurableEquiv_normOneToPositiveQuotient F G h q
    rw [hcomp]
    rfl
  · exact (quotientMeasurableEquiv F G h).measurable
  · exact measurable_from_quotient.mpr
      ((LeftCosetSpace.measurable_mk (positiveRationalSubgroup F G T i)).comp
        measurable_subtype_coe)

theorem map_quotientHomeomorph (h : subgroup F G S j = imageSubgroup F T G i) :
    (positiveRationalQuotientHaarMeasure F G T i).map (quotientHomeomorph F G h) =
      quotientHaarMeasure F G S j :=
  (measurePreserving_quotientMeasurableEquiv F G h).map_eq

variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]

include hi in
/-- The combined restriction subgroup is closed. -/
theorem isClosed_rationalSubgroup (h : subgroup F G S j = imageSubgroup F T G i)
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) :
    IsClosed (rationalSubgroup F G S j : Set (AdelicGroupPoints F G)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  rw [rationalSubgroup_eq F G h]
  exact isClosed_positiveRationalSubgroup F G T i hi I e hc

include hi in
theorem quotient_t2Space (h : subgroup F G S j = imageSubgroup F T G i)
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) : T2Space (Quotient F G S j) := by
  let : IsClosed (rationalSubgroup F G S j : Set (AdelicGroupPoints F G)) :=
    isClosed_rationalSubgroup F G hi h hc hT
  infer_instance

include hi in
/-- The inherited quotient sigma algebra is Borel for the actual quotient topology. -/
theorem quotient_borelSpace (h : subgroup F G S j = imageSubgroup F T G i)
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) : BorelSpace (Quotient F G S j) := by
  let := quotient_t2Space F G hi h hc hT
  exact LeftCosetSpace.quotient_borelSpace (rationalSubgroup F G S j)

/-- The norm-one principal quotient is homeomorphic to the restriction quotient by
inclusion of representatives. -/
def normOneQuotientHomeomorph (h : subgroup F G S j = imageSubgroup F T G i)
    (I : Type) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    (hc : IsCentral i) :
    AdelicGroupPoints.NormOneRationalQuotient F G ≃ₜ Quotient F G S j :=
  (positiveQuotientHomeomorph F G T i hi I e hc).trans (quotientHomeomorph F G h)

@[simp] theorem coe_normOneQuotientHomeomorph (h : subgroup F G S j = imageSubgroup F T G i)
    (I : Type) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    (hc : IsCentral i) :
    ⇑(normOneQuotientHomeomorph F G hi h I e hc) = normOneToQuotient F G S j := by
  funext q
  exact quotientMeasurableEquiv_normOneToPositiveQuotient F G h q

/-- Full subgroup Haar on the combined restriction subgroup, moved from the intrinsic
positive-torus normalization by the identity on ambient points. -/
def subgroupHaarMeasure (h : subgroup F G S j = imageSubgroup F T G i)
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) : Measure (rationalSubgroup F G S j) :=
  (intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hc hT).map
    (MulEquiv.subgroupCongr (rationalSubgroup_eq F G h).symm)

theorem subgroupHaarMeasure_isMulRightInvariant (h : subgroup F G S j = imageSubgroup F T G i)
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) :
    IsMulRightInvariant (subgroupHaarMeasure F G hi h hc hT) := by
  let := intrinsicPositiveRationalSubgroupHaarMeasure_isMulRightInvariant F G T i hi hc hT
  exact LeftCosetSpace.isMulRightInvariant_map_subgroupCongr _ _

theorem subgroupHaarMeasure_isHaarMeasure (h : subgroup F G S j = imageSubgroup F T G i)
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) :
    (subgroupHaarMeasure F G hi h hc hT).IsHaarMeasure := by
  let := intrinsicPositiveRationalSubgroupHaarMeasure_isHaarMeasure F G T i hi hc hT
  exact LeftCosetSpace.isHaarMeasure_map_subgroupCongr _ _

local instance (h : subgroup F G S j = imageSubgroup F T G i)
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) :
    IsMulRightInvariant (subgroupHaarMeasure F G hi h hc hT) :=
  subgroupHaarMeasure_isMulRightInvariant F G hi h hc hT

/-- Orbital integration over the combined restriction subgroup. -/
def rationalQuotientAverage (h : subgroup F G S j = imageSubgroup F T G i)
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) (f : AdelicGroupPoints F G → ℂ) :
    Quotient F G S j → ℂ :=
  Langlands.QuotientIntegration.quotientAverage (rationalSubgroup F G S j)
    (subgroupHaarMeasure F G hi h hc hT) f

@[simp] theorem rationalQuotientAverage_mk (h : subgroup F G S j = imageSubgroup F T G i)
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) (f : AdelicGroupPoints F G → ℂ)
    (g : AdelicGroupPoints F G) :
    rationalQuotientAverage F G hi h hc hT f (LeftCosetSpace.mk (rationalSubgroup F G S j) g) =
      ∫ k : rationalSubgroup F G S j, f (k.val * g) ∂subgroupHaarMeasure F G hi h hc hT :=
  rfl

/-- The orbital average agrees with the intrinsic positive-torus average on representatives. -/
theorem rationalQuotientAverage_quotientHomeomorph (h : subgroup F G S j = imageSubgroup F T G i)
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) (f : AdelicGroupPoints F G → ℂ)
    (q : PositiveRationalQuotient F G T i) :
    rationalQuotientAverage F G hi h hc hT f (quotientHomeomorph F G h q) =
      intrinsicPositiveRationalQuotientAverage F G T i hi hc hT f q := by
  induction q using Quotient.inductionOn with
  | _ g =>
    change rationalQuotientAverage F G hi h hc hT f
      (quotientHomeomorph F G h (LeftCosetSpace.mk (positiveRationalSubgroup F G T i) g)) = _
    rw [quotientHomeomorph_mk, rationalQuotientAverage_mk]
    change (∫ k : rationalSubgroup F G S j, f (k.val * g)
      ∂(intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hc hT).map
        (MulEquiv.subgroupCongr (rationalSubgroup_eq F G h).symm)) =
          ∫ k : positiveRationalSubgroup F G T i, f (k.val * g)
            ∂intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hc hT
    have hm : MeasurableEmbedding (MulEquiv.subgroupCongr (rationalSubgroup_eq F G h).symm) :=
      (MeasurableEquiv.mk (MulEquiv.subgroupCongr (rationalSubgroup_eq F G h).symm).toEquiv
        (measurable_subtype_coe.subtype_mk) (measurable_subtype_coe.subtype_mk)).measurableEmbedding
    exact hm.integral_map (fun k : rationalSubgroup F G S j => f (k.val * g))

section Weil

variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]

/-- The quotient measure is Weil compatible with ambient Haar and the transported full
subgroup Haar normalization. -/
theorem quotientHaarMeasure_isCompatible (h : subgroup F G S j = imageSubgroup F T G i)
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) :
    IsCompatible (rationalSubgroup F G S j)
      (Measure.haar : Measure (AdelicGroupPoints F G))
      (subgroupHaarMeasure F G hi h hc hT) (quotientHaarMeasure F G S j) := by
  let := intrinsicPositiveRationalSubgroupHaarMeasure_isMulRightInvariant F G T i hi hc hT
  exact LeftCosetSpace.isCompatible_congrSubgroup (rationalSubgroup_eq F G h).symm _
    (intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hc hT)
    (subgroupHaarMeasure F G hi h hc hT) (positiveRationalQuotientHaarMeasure F G T i)
    (quotientHaarMeasure F G S j) rfl (map_quotientHomeomorph F G h)
    (intrinsicPositiveRationalQuotientHaarMeasure_isCompatible F G T i hi hc hT)

/-- Orbital averages of compact tests are integrable on the restriction quotient. -/
theorem integrable_rationalQuotientAverage (h : subgroup F G S j = imageSubgroup F T G i)
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)
    (f : AdelicGroupPoints F G → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (rationalQuotientAverage F G hi h hc hT f) (quotientHaarMeasure F G S j) :=
  (quotientHaarMeasure_isCompatible F G hi h hc hT).averaging_integrable f hf hfc

/-- The Weil integration formula on the restriction quotient. -/
theorem integral_rationalQuotientAverage (h : subgroup F G S j = imageSubgroup F T G i)
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)
    (f : AdelicGroupPoints F G → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    (∫ q, rationalQuotientAverage F G hi h hc hT f q ∂quotientHaarMeasure F G S j) =
      ∫ g, f g ∂(Measure.haar : Measure (AdelicGroupPoints F G)) :=
  (quotientHaarMeasure_isCompatible F G hi h hc hT).integral_formula f hf hfc

end Weil

variable {T' : CommGroupScheme (Spec (CommRingCat.of F))} {i' : T'.toGrp ⟶ G}
variable (hi' : Function.Injective (characterRestrict i'))
variable [(characterRestrict i').range.FiniteIndex]

/-- The transported subgroup Haar measure does not depend on the split component of `G`. -/
theorem subgroupHaarMeasure_eq_of_splitComponents
    (h : subgroup F G S j = imageSubgroup F T G i)
    (h' : subgroup F G S j = imageSubgroup F T' G i')
    (hs : IsSplitComponent i) (hs' : IsSplitComponent i') :
    subgroupHaarMeasure F G hi h hs.1.2 hs.1.1.1 =
      subgroupHaarMeasure F G hi' h' hs'.1.2 hs'.1.1.1 := by
  have hp := measurePreserving_splitComponentSubgroupEquiv_intrinsic
    F G T i hi T' i' hi' hs hs'
  have hm : Measurable (MulEquiv.subgroupCongr (rationalSubgroup_eq F G h').symm) :=
    measurable_subtype_coe.subtype_mk
  unfold subgroupHaarMeasure
  rw [← hp.map_eq, Measure.map_map hm hp.measurable]
  rfl

section Comparison

omit [(characterRestrict i).range.FiniteIndex] in
/-- The comparison statement identifies the restriction image with the positive image of any
split component of `G`. -/
theorem subgroup_eq_of_comparison (hcomp : ComparisonStatement)
    (hj : IsSplitComponent j) (hs : IsSplitComponent i) :
    subgroup F G S j = imageSubgroup F T G i :=
  hcomp F G S j T i hj hs

variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]

/-- Weil compatibility on the restriction quotient for split components of the restriction
and of `G`, assuming the comparison statement. -/
theorem quotientHaarMeasure_isCompatible_of_comparison (hcomp : ComparisonStatement)
    (hj : IsSplitComponent j) (hs : IsSplitComponent i) :
    IsCompatible (rationalSubgroup F G S j)
      (Measure.haar : Measure (AdelicGroupPoints F G))
      (subgroupHaarMeasure F G hi (subgroup_eq_of_comparison F G hcomp hj hs) hs.1.2 hs.1.1.1)
      (quotientHaarMeasure F G S j) :=
  quotientHaarMeasure_isCompatible F G hi _ hs.1.2 hs.1.1.1

end Comparison

end RestrictionSplitCentre

end Langlands.Global
