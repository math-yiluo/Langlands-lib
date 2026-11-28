import Langlands.BaseChange.TwistedLeviPaleyWienerStatements
import Langlands.BaseChange.TwistedCharacter.InducedTest
import Langlands.BaseChange.TwistedCharacter.SemidirectReduction
import Langlands.BaseChange.GeneralLinearFiniteAlgebra
import Langlands.Group.GL.ConjugatePairRefinementRankProof
import Langlands.Analysis.Local.ProductModularCharacter
import Langlands.AllField.Representation.Parabolic.QuotientCompactProof
import Langlands.LocalField.FiniteExtensionModuleTopology
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
import Mathlib.Topology.Metrizable.Urysohn

/-! # Twisted induction transfer inside a block Levi -/

noncomputable section

open scoped Topology

namespace Langlands.BaseChange.TwistedLeviPaleyWiener

open MeasureTheory GeneralLinear ConjugatePairRefinementRankProof HarmonicAnalysis

universe u v z

section Projection

variable {E : Type v} [Field E] {n : ℕ} {B C : BlockShape n}

/-- Inclusion of standard parabolics implies inclusion of their allowed entry positions. -/
theorem coordinateBlock_le_of_parabolic_le (hCB : C.parabolic E ≤ B.parabolic E)
    {x y : Fin n} (hxy : C.coordinateBlock x ≤ C.coordinateBlock y) :
    B.coordinateBlock x ≤ B.coordinateBlock y := by
  by_contra! hlt
  have hne : x ≠ y := fun h => by simp [h] at hlt
  let g := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection x y (1 : E))
    (by rw [Matrix.det_transvection_of_ne _ _ hne]; exact one_ne_zero)
  have hgC : g ∈ C.parabolic E := by
    rw [mem_parabolic_iff_blk]
    intro i j hij
    have hij' : i ≠ j := fun h => by simp [h] at hij
    have hs : ¬ (x = i ∧ y = j) := by
      rintro ⟨rfl, rfl⟩
      exact (not_lt_of_ge hxy) hij
    change Matrix.transvection x y (1 : E) i j = 0
    simp [Matrix.transvection, Matrix.one_apply_ne hij',
      Matrix.single_apply_of_ne _ _ _ _ _ hs]
  have hz := (mem_parabolic_iff_blk B g).mp (hCB hgC) x y hlt
  change Matrix.transvection x y (1 : E) x y = 0 at hz
  simp [Matrix.transvection, Matrix.one_apply_ne hne] at hz

private theorem leviEmbedding_apply_of_coordinateBlock_ne (D : BlockShape n) (m : D.Levi E)
    {x y : Fin n} (hxy : D.coordinateBlock x ≠ D.coordinateBlock y) :
    D.leviEmbedding E m x y = 0 := by
  obtain ⟨⟨i, a⟩, rfl⟩ := D.indexEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := D.indexEquiv.surjective y
  exact D.leviEmbedding_apply_ne E m a b (by
    change D.coordinateBlock (D.index i a) ≠ D.coordinateBlock (D.index j b) at hxy
    simpa only [blk_index] using hxy)

private theorem coarseProjection_fineEmbedding (hCB : C.parabolic E ≤ B.parabolic E)
    (m : C.Levi E) :
    B.leviEmbedding E (B.leviProjection E (Subgroup.inclusion hCB (C.leviInParabolic E m))) =
      C.leviEmbedding E m := by
  apply Units.ext
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
  change B.leviEmbedding E _ (B.index i a) (B.index j b) =
    C.leviEmbedding E m (B.index i a) (B.index j b)
  by_cases hij : i = j
  · subst j
    rw [B.leviEmbedding_apply_same, B.leviProjection_apply]
    rfl
  · rw [B.leviEmbedding_apply_ne _ _ _ _ hij]
    symm
    apply leviEmbedding_apply_of_coordinateBlock_ne
    intro h
    apply hij
    have h' := le_antisymm (coordinateBlock_le_of_parabolic_le hCB h.le)
      (coordinateBlock_le_of_parabolic_le hCB h.ge)
    simpa only [blk_index] using h'

/-- The finer block diagonal subgroup embeds in the coarser block Levi. -/
def relLeviSection (hCB : C.parabolic E ≤ B.parabolic E) :
    C.Levi E →* relParabolic E B C :=
  let f := (B.leviProjection E).comp ((Subgroup.inclusion hCB).comp (C.leviInParabolic E))
  f.codRestrict (relParabolic E B C) fun m => by
    change B.leviEmbedding E (f m) ∈ C.parabolic E
    rw [show B.leviEmbedding E (f m) = C.leviEmbedding E m from
      coarseProjection_fineEmbedding hCB m]
    exact (C.leviInParabolic E m).property

@[simp]
theorem relProjection_section (hCB : C.parabolic E ≤ B.parabolic E) (m : C.Levi E) :
    relProjection E B C (relLeviSection hCB m) = m := by
  have he : relEmbedding E B C (relLeviSection hCB m) = C.leviInParabolic E m :=
    Subtype.ext (coarseProjection_fineEmbedding hCB m)
  rw [relProjection_apply, he, C.leviProjection_section]

variable [TopologicalSpace E] [IsTopologicalRing E]

theorem continuous_relProjection (B C : BlockShape n) : Continuous (relProjection E B C) :=
  (C.leviProjectionContinuous E).continuous.comp
    (((B.leviEmbeddingContinuous E).continuous.comp continuous_subtype_val).subtype_mk _)

omit [IsTopologicalRing E] in
theorem isClosed_relParabolic [T2Space E] (B C : BlockShape n) :
    IsClosed (relParabolic E B C : Set (B.Levi E)) :=
  (C.isClosed_parabolic E).preimage (B.leviEmbeddingContinuous E).continuous

theorem continuous_relLeviSection (hCB : C.parabolic E ≤ B.parabolic E) :
    Continuous (relLeviSection hCB) :=
  ((B.leviProjectionContinuous E).continuous.comp
    ((C.leviEmbeddingContinuous E).continuous.subtype_mk _)).subtype_mk _

theorem isOpenMap_relProjection (hCB : C.parabolic E ≤ B.parabolic E) :
    IsOpenMap (relProjection E B C) := by
  apply (IsTopologicalGroup.isOpenMap_iff_nhds_one (f := relProjection E B C)).mpr
  have hs : Filter.map (relLeviSection hCB) (𝓝 1) ≤ 𝓝 1 := by
    have ht := (continuous_relLeviSection hCB).continuousAt (x := (1 : C.Levi E))
    simpa only [ContinuousAt, Filter.Tendsto, map_one] using ht
  have hm : Filter.map (relProjection E B C) (Filter.map (relLeviSection hCB) (𝓝 1)) ≤
      Filter.map (relProjection E B C) (𝓝 1) := Filter.map_mono hs
  simpa only [Filter.map_map, Function.comp_def, relProjection_section, Filter.map_id'] using hm

end Projection

section Local

variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] {n : ℕ}

/-- Every coset meets the product of the integral subgroups of the outer blocks. -/
theorem compactSpace_relParabolic_quotient (B C : BlockShape n) :
    CompactSpace (Induction.LeftQuotient (relParabolic E B C)) := by
  let K : Set (B.Levi E) := Set.univ.pi fun i =>
    Iwasawa.integralRange (ValuativeRel.valuation E) (B.size i)
  have hK : IsCompact K :=
    isCompact_univ_pi fun i => AllField.Parabolic.isCompact_integralRange
      (LocalFieldData.ofInstances E) (B.size i)
  have hcover : Induction.quotientMap (relParabolic E B C) '' K = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    induction q using Quotient.inductionOn with
    | h m =>
      choose k hk htri using fun i =>
        Iwasawa.exists_mul_upperTriangular (ValuativeRel.valuation E) (B.size i) (m i)
      refine ⟨k⁻¹, fun i _ => inv_mem (hk i), Quotient.sound ?_⟩
      change QuotientGroup.rightRel (relParabolic E B C) k⁻¹ m
      rw [QuotientGroup.rightRel_apply, inv_inv]
      change B.leviEmbedding E (m * k) ∈ C.parabolic E
      apply C.mem_parabolic_of_isUpperTriangular
      intro x y hyx
      obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
      obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
      change B.leviEmbedding E (m * k) (B.index i a) (B.index j b) = 0
      by_cases hij : i = j
      · subst j
        rw [B.leviEmbedding_apply_same]
        exact htri i ((Geometric.index_strictMono B i).lt_iff_lt.mp hyx)
      · exact B.leviEmbedding_apply_ne E _ a b hij
  exact ⟨hcover ▸ hK.image continuous_quotient_mk'⟩

/-- Finite products of general linear groups have two-sided Haar measure. -/
theorem levi_haar_rightInvariant (B : BlockShape n)
    [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)]
    (ν : Measure (B.Levi E)) [ν.IsHaarMeasure] : ν.IsMulRightInvariant := by
  let : ∀ i, T2Space (GeneralLinear (B.size i) E) :=
    fun i => LocalFieldTopology.generalLinear_t2Space E (B.size i)
  let : ∀ i, LocallyCompactSpace (GeneralLinear (B.size i) E) :=
    fun i => LocalFieldTopology.generalLinear_locallyCompactSpace E (B.size i)
  let : ∀ i, SecondCountableTopology (GeneralLinear (B.size i) E) :=
    fun i => LocalFieldTopology.generalLinear_secondCountableTopology E (B.size i)
  let : SecondCountableTopology (B.Levi E) := inferInstance
  let : SigmaCompactSpace (B.Levi E) := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace (B.Levi E) := inferInstance
  have hmod (m : B.Levi E) : Measure.modularCharacter m = 1 := by
    rw [ProductMeasure.modularCharacter_pi]
    apply Finset.prod_eq_one
    intro i _
    let G := GeneralLinear (B.size i) E
    let : MeasurableSpace G := borel G
    let : BorelSpace G := ⟨rfl⟩
    let : (Measure.haar : Measure G).IsMulRightInvariant :=
      generalLinear_haar_rightInvariant E (B.size i) Measure.haar
    change Measure.modularCharacterFun (m i) = 1
    rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure G)]
    have hf (μ : Measure G) [μ.IsHaarMeasure] (hμ : μ = Measure.haar) :
        μ.haarScalarFactor Measure.haar = 1 := by
      subst μ
      exact Measure.haarScalarFactor_self _
    exact hf _ (map_mul_right_eq_self _ _)
  refine ⟨fun m => ?_⟩
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul, show Measure.modularCharacterFun m = 1
    from hmod m, one_smul]

end Local

private theorem leviAut_pow_eq_one {F : Type u} [Field F] {E : Type v} [Field E]
    [Algebra F E] (σ : E ≃ₐ[F] E) {d n : ℕ} (hσ : σ ^ d = 1) (B : BlockShape n) :
    (leviAut σ B) ^ d = 1 := by
  have h (k : ℕ) (m : B.Levi E) (i : Fin B.length) :
      ((leviAut σ B) ^ k) m i = ((entrywiseAut σ (B.size i)) ^ k) (m i) := by
    induction k generalizing m with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ]
      change ((leviAut σ B) ^ k) (leviAut σ B m) i =
        ((entrywiseAut σ (B.size i)) ^ k) (entrywiseAut σ (B.size i) (m i))
      exact ih _
  ext m i
  rw [h, entrywiseAut_pow_eq_one σ hσ]
  rfl

/-- Apply the common inducing test on the relative parabolic of the Levi product. -/
theorem twistedLeviInductionTransfer : TwistedLeviInductionTransferStatement.{u,v,z} := by
  classical
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hE
  let := hE.1
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField_of_isModuleTopology F E
  let := LocalFieldTopology.t2Space E
  let : ∀ D : BlockShape n, MeasurableSpace (D.Levi E) := fun _ => borel _
  let : ∀ D : BlockShape n, BorelSpace (D.Levi E) := fun _ => ⟨rfl⟩
  let : ∀ D : BlockShape n, T2Space (D.Levi E) := levi_t2Space_of_finite F E
  let : ∀ D : BlockShape n, LocallyCompactSpace (D.Levi E) :=
    levi_locallyCompactSpace_of_finite F E
  let : ∀ D : BlockShape n, TotallyDisconnectedSpace (D.Levi E) :=
    levi_totallyDisconnectedSpace_of_finite F E
  intro B C hCB μ _ ν _
  let := compactSpace_relParabolic_quotient (E := E) B C
  let := levi_haar_rightInvariant C ν
  have htest := twistedInducedTest.{v,v,z} μ ν (leviAut σ B)
    (continuous_leviAut σ B) (continuous_leviAut_symm σ B)
    hE.pos (leviAut_pow_eq_one σ hE.pow_eq_one B) (relParabolic E B C)
    (isClosed_relParabolic B C) (leviAut_mem_relParabolic_iff σ B C)
    (relProjection E B C) (continuous_relProjection B C) (isOpenMap_relProjection hCB)
    (leviAut σ C) (relProjection_leviAut σ B C)
  let b := Module.Free.chooseBasis ℂ (SchwartzBruhat (B.Levi E))
  choose f hf using fun i => htest (b i)
  let CT := b.constr ℂ f
  refine ⟨CT, fun X _ _ Ξ hΞ A hI => b.ext fun i => ?_⟩
  change twistedDistribution ν Ξ hΞ A.toLinearMap (CT (b i)) = _
  rw [b.constr_basis ℂ f i]
  exact (hf i X Ξ hΞ A hI).symm

end Langlands.BaseChange.TwistedLeviPaleyWiener
