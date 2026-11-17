import Langlands.Representation.Jacquet.FixedVectorGeneratedCategory
import Langlands.Representation.Hecke.NondegenerateModuleEquivalenceProof
import Langlands.Representation.Category.Subquotients
import Langlands.Algebra.NonUnitalModuleIdempotentGenerated

/-! # Fixed-vector generation and generation by the normalized Hecke idempotent -/

noncomputable section

universe u v

open CategoryTheory MeasureTheory

namespace Langlands.Hecke

open Langlands.Algebra

variable {G : Type u} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

/-- The normalized compact-open indicator as an idempotent of the Haar Hecke algebra. -/
def compactOpenIdempotent (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    Idempotent (HeckeAlgebra μ) :=
  ⟨HeckeAlgebra.normalizedIndicator μ K hK,
    HeckeAlgebra.normalizedIndicator_idempotent μ K hK⟩

/-- Generation by fixed vectors, expressed through all actual subrepresentations. -/
abbrev fixedVectorGeneratedProperty (K : OpenSubgroup G) :
    ObjectProperty (SmoothRep.{0, u, v} ℂ G) :=
  Langlands.Jacquet.fixedVectorGenerated K.toSubgroup

namespace IdempotentGenerationBridge

variable (V : SmoothRep.{0, u, v} ℂ G)

/-- Every original Hecke submodule is complex-linear and invariant under the group. -/
def toSubrepresentation
    (T : @NonUnitalSubmodule (HeckeAlgebra μ) V _ _
      (heckeNonUnitalModule μ V.representation V.isSmooth)) :
    Subrepresentation V.representation := by
  letI := heckeNonUnitalModule μ V.representation V.isSmooth
  refine
    { toSubmodule :=
        { toAddSubmonoid := T.toAddSubgroup.toAddSubmonoid
          smul_mem' := ?_ }
      apply_mem_toSubmodule := ?_ }
  · intro c m hm
    obtain ⟨e, he⟩ := heckeNonUnitalModule_isNondegenerate μ V.representation V.isSmooth m
    have hc : (c • (e : HeckeAlgebra μ)) • m = c • m := by
      rw [NonUnitalModule.ofLinearEndHom_smul_assoc, he]
    exact hc ▸ T.smul_mem' (c • (e : HeckeAlgebra μ)) hm
  · intro g m hm
    obtain ⟨e, he⟩ := heckeNonUnitalModule_isNondegenerate μ V.representation V.isSmooth m
    have hg : NondegenerateEquivalence.translate μ g (e : HeckeAlgebra μ) • m =
        V.representation g m := by
      change integratedAction μ V.representation V.isSmooth
        (TestFunction.leftTranslate g (HeckeAlgebra.toTestFunction μ (e : HeckeAlgebra μ))) m = _
      rw [integratedAction_leftTranslate]
      exact congrArg (V.representation g) he
    exact hg ▸ T.smul_mem' _ hm

/-- Every subrepresentation is stable under the integrated Hecke action. -/
def toHeckeSubmodule (T : Subrepresentation V.representation) :
    @NonUnitalSubmodule (HeckeAlgebra μ) V _ _
      (heckeNonUnitalModule μ V.representation V.isSmooth) := by
  letI := heckeNonUnitalModule μ V.representation V.isSmooth
  refine { toAddSubgroup := T.toSubmodule.toAddSubgroup
           smul_mem' := ?_ }
  intro a m hm
  let W := SmoothRep.subrepresentation V T
  have h := ((heckeNondegenerateModuleFunctor μ).map (SmoothRep.subtype V T)).hom.map_smul
    a (⟨m, hm⟩ : W)
  change Subtype.val (heckeAction μ W.representation W.isSmooth a ⟨m, hm⟩) =
    heckeAction μ V.representation V.isSmooth a m at h
  change heckeAction μ V.representation V.isSmooth a m ∈ T
  rw [← h]
  exact (heckeAction μ W.representation W.isSmooth a ⟨m, hm⟩).property

omit [T2Space G] [LocallyCompactSpace G] in
/-- The original idempotent-fixed additive subgroup is the compact-open fixed space. -/
theorem mem_fixedPart_iff (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (m : V) :
    (letI := heckeNonUnitalModule μ V.representation V.isSmooth
     m ∈ NonUnitalModuleCorner.fixedPart (compactOpenIdempotent μ K hK) V) ↔
      m ∈ fixedVectors V.representation K.toSubgroup := by
  constructor
  · intro hm
    have hm' : heckeAction μ V.representation V.isSmooth
        (HeckeAlgebra.normalizedIndicator μ K hK) m = m := hm
    rw [← hm']
    exact heckeAction_normalizedIndicator_mem μ V.representation V.isSmooth K hK m
  · exact heckeAction_normalizedIndicator_of_fixed μ V.representation V.isSmooth K hK

end IdempotentGenerationBridge

omit [T2Space G] in
/-- Generation by `K`-fixed vectors is exactly generation by the normalized indicator. -/
theorem fixedVectorGenerated_iff_idempotentGenerated
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (V : SmoothRep.{0, u, v} ℂ G) :
    fixedVectorGeneratedProperty K V ↔
      NonUnitalModuleIdempotentGenerated.generatedProperty
        (compactOpenIdempotent μ K hK) ((heckeNondegenerateModuleFunctor μ).obj V) := by
  let := heckeNonUnitalModule μ V.representation V.isSmooth
  change fixedVectorGeneratedProperty K V ↔
    NonUnitalModuleIdempotentGenerated.IsGeneratedByIdempotent
      (compactOpenIdempotent μ K hK) V
  rw [NonUnitalModuleIdempotentGenerated.isGenerated_iff_least]
  constructor
  · intro h T hT m
    have htop := h (IdempotentGenerationBridge.toSubrepresentation μ V T) (by
      intro n hn
      exact hT ((IdempotentGenerationBridge.mem_fixedPart_iff μ V K hK n).2 hn))
    have hm : m ∈ IdempotentGenerationBridge.toSubrepresentation μ V T := by
      rw [htop]
      trivial
    exact hm
  · intro h T hT
    apply top_unique
    intro m _
    exact h (IdempotentGenerationBridge.toHeckeSubmodule μ V T) (by
      intro n hn
      change n ∈ T
      exact hT ((IdempotentGenerationBridge.mem_fixedPart_iff μ V K hK n).1 hn)) m

end Langlands.Hecke
