import Langlands.Analysis.Local.SubgroupCompactOpenHaar
import Langlands.Representation.Plancherel.StandardIntertwiningFirstFactorMass

/-! # The source Haar scale on actual standard-intertwining factors -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization

open Haar QuotientIntegration

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U₀ U₁ U₂ V W : Subgroup G}

/-- The actual intersection includes into the original ambient group by
forgetting its two subtype wrappers. -/
def intersectionAmbientHom (A B : Subgroup G) : A.subgroupOf B →* G :=
  B.subtype.comp (A.subgroupOf B).subtype

omit [IsTopologicalGroup G] in
/-- Closedness of both original subgroups gives a closed embedding of the
actual intersection carrier. -/
theorem intersectionAmbientHom_isClosedEmbedding
    (A B : Subgroup G) (hA : IsClosed (A : Set G)) (hB : IsClosed (B : Set G)) :
    Topology.IsClosedEmbedding (intersectionAmbientHom A B : A.subgroupOf B → G) :=
  hB.isClosedEmbedding_subtypeVal.comp
    (hA.preimage (continuous_subtype_val : Continuous (Subtype.val : B → G))).isClosedEmbedding_subtypeVal

variable (Q : OpenSubgroup G) (hQ : IsCompact (Q : Set G))

section Intersection

variable (A B : Subgroup G) (hA : IsClosed (A : Set G)) (hB : IsClosed (B : Set G))
  [MeasurableSpace (A.subgroupOf B)] [BorelSpace (A.subgroupOf B)]

/-- Haar measure on an actual intersection, normalized by its inverse image
of the single original ambient compact open. -/
def sourceIntersectionHaar : Measure (A.subgroupOf B) :=
  compactOpenHaarAlong Q hQ (intersectionAmbientHom A B)
    (intersectionAmbientHom_isClosedEmbedding A B hA hB)

instance sourceIntersectionHaar_isHaarMeasure :
    IsHaarMeasure (sourceIntersectionHaar Q hQ A B hA hB) := by
  unfold sourceIntersectionHaar
  infer_instance

instance sourceIntersectionHaar_regular :
    (sourceIntersectionHaar Q hQ A B hA hB).Regular := by
  unfold sourceIntersectionHaar
  infer_instance

@[simp] theorem sourceIntersectionHaar_mass :
    sourceIntersectionHaar Q hQ A B hA hB
      {a : A.subgroupOf B | a.val.val ∈ Q} = 1 :=
  compactOpenHaarAlong_mass Q hQ (intersectionAmbientHom A B)
    (intersectionAmbientHom_isClosedEmbedding A B hA hB)

end Intersection

variable (D : OrderedSubgroupFactorization U₀ U₁ U₂ V W)

section Kernel

variable (hU₀ : IsClosed (U₀ : Set G)) (hU₂ : IsClosed (U₂ : Set G))
  [MeasurableSpace (U₀.subgroupOf U₂)] [BorelSpace (U₀.subgroupOf U₂)]
  [MeasurableSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]

/-- Intrinsic source Haar on the actual nested endpoint kernel. The composite
homomorphism is the literal ambient inclusion, since the equivalence only
forgets subtype wrappers. -/
def sourceNestedKernelHaar :
    Measure ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) :=
  compactOpenHaarAlong Q hQ
    ((intersectionAmbientHom U₀ U₂).comp D.intersectionKernelEquiv.toMonoidHom)
    ((intersectionAmbientHom_isClosedEmbedding U₀ U₂ hU₀ hU₂).comp
      D.intersectionKernelEquiv.isClosedEmbedding)

instance sourceNestedKernelHaar_isHaarMeasure :
    IsHaarMeasure (D.sourceNestedKernelHaar Q hQ hU₀ hU₂) := by
  unfold sourceNestedKernelHaar
  infer_instance

instance sourceNestedKernelHaar_regular :
    (D.sourceNestedKernelHaar Q hQ hU₀ hU₂).Regular := by
  unfold sourceNestedKernelHaar
  infer_instance

omit [MeasurableSpace (U₀.subgroupOf U₂)] [BorelSpace (U₀.subgroupOf U₂)] in
@[simp] theorem sourceNestedKernelHaar_mass :
    D.sourceNestedKernelHaar Q hQ hU₀ hU₂
      {h : (U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂) |
        h.val.val.val ∈ Q} = 1 :=
  compactOpenHaarAlong_mass Q hQ _ _

variable [LocallyCompactSpace G]

/-- Transport of the actual nested kernel gives exactly the source Haar on
the original endpoint intersection. -/
theorem intersectionKernelMeasure_source :
    D.intersectionKernelMeasure (D.sourceNestedKernelHaar Q hQ hU₀ hU₂) =
      sourceIntersectionHaar Q hQ U₀ U₂ hU₀ hU₂ := by
  exact (measurePreserving_compactOpenHaarAlong Q hQ
    ((intersectionAmbientHom U₀ U₂).comp D.intersectionKernelEquiv.toMonoidHom)
    ((intersectionAmbientHom_isClosedEmbedding U₀ U₂ hU₀ hU₂).comp
      D.intersectionKernelEquiv.isClosedEmbedding)
    (intersectionAmbientHom U₀ U₂)
    (intersectionAmbientHom_isClosedEmbedding U₀ U₂ hU₀ hU₂)
    D.intersectionKernelEquiv (fun _ => rfl)).map_eq

end Kernel

section FirstComplement

variable (hV : IsClosed (V : Set G))
  [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]

/-- Intrinsic source Haar on the actual nested first complement. -/
def sourceNestedComplementHaar :
    Measure ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) :=
  compactOpenHaarAlong Q hQ
    (V.subtype.comp D.intersectionComplementEquiv.toMonoidHom)
    (hV.isClosedEmbedding_subtypeVal.comp D.intersectionComplementEquiv.isClosedEmbedding)

instance sourceNestedComplementHaar_isHaarMeasure :
    IsHaarMeasure (D.sourceNestedComplementHaar Q hQ hV) := by
  unfold sourceNestedComplementHaar
  exact compactOpenHaarAlong_isHaarMeasure Q hQ _ _

instance sourceNestedComplementHaar_regular :
    (D.sourceNestedComplementHaar Q hQ hV).Regular := by
  unfold sourceNestedComplementHaar
  exact compactOpenHaarAlong_regular Q hQ _ _

omit [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem sourceNestedComplementHaar_mass :
    D.sourceNestedComplementHaar Q hQ hV
      {k : (V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂) |
        k.val.val.val ∈ Q} = 1 :=
  compactOpenHaarAlong_mass Q hQ _ _

/-- The nested complement's compact open is the inverse image of the same
original ambient compact open. -/
def sourceNestedComplementCompactOpen :
    OpenSubgroup ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) :=
  compactOpenPreimage Q
    (V.subtype.comp D.intersectionComplementEquiv.toMonoidHom)
    (hV.isClosedEmbedding_subtypeVal.comp D.intersectionComplementEquiv.isClosedEmbedding)

variable (hU₀ : IsClosed (U₀ : Set G)) (hU₁ : IsClosed (U₁ : Set G))
  (hU₂ : IsClosed (U₂ : Set G))
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace (U₀.subgroupOf U₂)] [BorelSpace (U₀.subgroupOf U₂)]
  [MeasurableSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]

/-- The middle intersection's compact open is its actual inverse image of
the fixed original ambient compact open. -/
def sourceMiddleCompactOpen : OpenSubgroup (U₁.subgroupOf U₂) :=
  compactOpenPreimage Q (intersectionAmbientHom U₁ U₂)
    (intersectionAmbientHom_isClosedEmbedding U₁ U₂ hU₁ hU₂)

omit [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace (U₀.subgroupOf U₂)] [BorelSpace (U₀.subgroupOf U₂)] in
/-- Every volume in the intersection correction scalar is one at the
common ambient source scale. -/
theorem intersectionFactorScalar_source :
    compactOpenFactorScalar
      ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
      ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
      (sourceIntersectionHaar Q hQ U₁ U₂ hU₁ hU₂)
      (D.sourceNestedKernelHaar Q hQ hU₀ hU₂)
      (D.sourceNestedComplementHaar Q hQ hV)
      (sourceMiddleCompactOpen Q hU₁ hU₂)
      (D.sourceNestedComplementCompactOpen Q hV) = 1 := by
  have hS : sourceIntersectionHaar Q hQ U₁ U₂ hU₁ hU₂
      (sourceMiddleCompactOpen Q hU₁ hU₂ : Set (U₁.subgroupOf U₂)) = 1 :=
    sourceIntersectionHaar_mass Q hQ U₁ U₂ hU₁ hU₂
  have hH : D.sourceNestedKernelHaar Q hQ hU₀ hU₂
      {h : (U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂) |
        h.val ∈ sourceMiddleCompactOpen Q hU₁ hU₂} = 1 :=
    compactOpenHaarAlong_mass Q hQ _ _
  have hB : D.sourceNestedComplementHaar Q hQ hV
      (D.sourceNestedComplementCompactOpen Q hV :
        Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))) = 1 :=
    compactOpenHaarAlong_mass Q hQ _ _
  simp only [compactOpenFactorScalar, hS, hH, hB,
    ENNReal.toNNReal_one, one_mul, div_one]

variable [LocallyCompactSpace G]

omit [MeasurableSpace (U₀.subgroupOf U₂)] [BorelSpace (U₀.subgroupOf U₂)] in
/-- The explicitly normalized intersection factor is the original first
complement's source Haar, with no residual scalar. -/
theorem intersectionNormalizedFactor_source :
    D.intersectionNormalizedFactor
      (sourceIntersectionHaar Q hQ U₁ U₂ hU₁ hU₂)
      (D.sourceNestedKernelHaar Q hQ hU₀ hU₂)
      (D.sourceNestedComplementHaar Q hQ hV)
      (sourceMiddleCompactOpen Q hU₁ hU₂)
      (D.sourceNestedComplementCompactOpen Q hV) =
        subgroupCompactOpenHaar Q hQ V hV := by
  unfold intersectionNormalizedFactor compactOpenFactorMeasure
  rw [D.intersectionFactorScalar_source Q hQ hV hU₀ hU₁ hU₂, one_smul]
  exact (measurePreserving_compactOpenHaarAlong Q hQ
    (V.subtype.comp D.intersectionComplementEquiv.toMonoidHom)
    (hV.isClosedEmbedding_subtypeVal.comp D.intersectionComplementEquiv.isClosedEmbedding)
    V.subtype hV.isClosedEmbedding_subtypeVal
    D.intersectionComplementEquiv (fun _ => rfl)).map_eq

end FirstComplement

section SecondComplement

variable (hW : IsClosed (W : Set G))
  [MeasurableSpace W] [BorelSpace W]
  [MeasurableSpace (W.subgroupOf U₂)] [BorelSpace (W.subgroupOf U₂)]

/-- Intrinsic source Haar on the actual second complement. -/
def sourceSecondComplementHaar : Measure (W.subgroupOf U₂) :=
  compactOpenHaarAlong Q hQ
    (W.subtype.comp D.secondComplementEquiv.toMonoidHom)
    (hW.isClosedEmbedding_subtypeVal.comp D.secondComplementEquiv.isClosedEmbedding)

instance sourceSecondComplementHaar_isHaarMeasure :
    IsHaarMeasure (D.sourceSecondComplementHaar Q hQ hW) := by
  unfold sourceSecondComplementHaar
  exact compactOpenHaarAlong_isHaarMeasure Q hQ _ _

instance sourceSecondComplementHaar_regular :
    (D.sourceSecondComplementHaar Q hQ hW).Regular := by
  unfold sourceSecondComplementHaar
  exact compactOpenHaarAlong_regular Q hQ _ _

omit [MeasurableSpace W] [BorelSpace W] in
@[simp] theorem sourceSecondComplementHaar_mass :
    D.sourceSecondComplementHaar Q hQ hW
      {l : W.subgroupOf U₂ | l.val.val ∈ Q} = 1 :=
  compactOpenHaarAlong_mass Q hQ _ _

/-- The actual second complement uses the same ambient compact open. -/
def sourceSecondComplementCompactOpen : OpenSubgroup (W.subgroupOf U₂) :=
  compactOpenPreimage Q
    (W.subtype.comp D.secondComplementEquiv.toMonoidHom)
    (hW.isClosedEmbedding_subtypeVal.comp D.secondComplementEquiv.isClosedEmbedding)

variable (hU₁ : IsClosed (U₁ : Set G)) (hU₂ : IsClosed (U₂ : Set G))
  [MeasurableSpace U₂] [BorelSpace U₂]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]

/-- The target compact open is the inverse image of the original ambient one. -/
def sourceTargetCompactOpen : OpenSubgroup U₂ :=
  compactOpenPreimage Q U₂.subtype hU₂.isClosedEmbedding_subtypeVal

omit [MeasurableSpace W] [BorelSpace W] in
/-- The second correction scalar is also one at the source scale. -/
theorem secondFactorScalar_source :
    compactOpenFactorScalar (U₁.subgroupOf U₂) (W.subgroupOf U₂)
      (subgroupCompactOpenHaar Q hQ U₂ hU₂)
      (sourceIntersectionHaar Q hQ U₁ U₂ hU₁ hU₂)
      (D.sourceSecondComplementHaar Q hQ hW)
      (sourceTargetCompactOpen Q hU₂)
      (D.sourceSecondComplementCompactOpen Q hW) = 1 := by
  have hT : subgroupCompactOpenHaar Q hQ U₂ hU₂
      (sourceTargetCompactOpen Q hU₂ : Set U₂) = 1 :=
    subgroupCompactOpenHaar_mass Q hQ U₂ hU₂
  have hI : sourceIntersectionHaar Q hQ U₁ U₂ hU₁ hU₂
      {h : U₁.subgroupOf U₂ | h.val ∈ sourceTargetCompactOpen Q hU₂} = 1 :=
    sourceIntersectionHaar_mass Q hQ U₁ U₂ hU₁ hU₂
  have hC : D.sourceSecondComplementHaar Q hQ hW
      (D.sourceSecondComplementCompactOpen Q hW : Set (W.subgroupOf U₂)) = 1 :=
    compactOpenHaarAlong_mass Q hQ _ _
  simp only [compactOpenFactorScalar, hT, hI, hC,
    ENNReal.toNNReal_one, one_mul, div_one]

variable [LocallyCompactSpace G]

/-- The explicitly normalized second factor is the original second
complement's source Haar. -/
theorem secondNormalizedFactor_source :
    D.secondNormalizedFactor
      (subgroupCompactOpenHaar Q hQ U₂ hU₂)
      (sourceIntersectionHaar Q hQ U₁ U₂ hU₁ hU₂)
      (D.sourceSecondComplementHaar Q hQ hW)
      (sourceTargetCompactOpen Q hU₂)
      (D.sourceSecondComplementCompactOpen Q hW) =
        subgroupCompactOpenHaar Q hQ W hW := by
  unfold secondNormalizedFactor compactOpenFactorMeasure
  rw [D.secondFactorScalar_source Q hQ hW hU₁ hU₂, one_smul]
  exact (measurePreserving_compactOpenHaarAlong Q hQ
    (W.subtype.comp D.secondComplementEquiv.toMonoidHom)
    (hW.isClosedEmbedding_subtypeVal.comp D.secondComplementEquiv.isClosedEmbedding)
    W.subtype hW.isClosedEmbedding_subtypeVal
    D.secondComplementEquiv (fun _ => rfl)).map_eq

end SecondComplement

end Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization
