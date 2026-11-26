import Langlands.BaseChange.TwistedCharacter.InducedRealization
import Langlands.BaseChange.TwistedCharacter.StandardTraceSpan
import Langlands.BaseChange.TwistedCharacter.TwistRegularity
import Langlands.Representation.Induction.RankCast
import Langlands.Group.GL.CountabilityProof

/-! # Proper and one-block standard twisted traces -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis MeasureTheory PadicField.TopologicalData

universe u v w z

variable {F : Type u} [Field F] [TopologicalSpace F] {p : ℕ} [Fact p.Prime]
  {E : PadicField.{v} p} [Algebra F E.Carrier] (T : E.TopologicalData)
  (hModule : letI := T.topology; IsModuleTopology F E.Carrier)
  (σ : E.Carrier ≃ₐ[F] E.Carrier)
  {n : ℕ} (t : T.TemperedLanglandsDatum.{w} n)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- An induced stable standard trace from at least two blocks lies in the
proper-induction span at every inducing carrier universe. -/
theorem temperedStandardTrace_mem_sigmaProperInducedSpan (ht : 2 ≤ t.shape.length) :
    letI := T.topology
    letI := T.localField
    letI := T.valuativeRel
    letI := hModule
    ∀ [T2Space (GeneralLinear n E.Carrier)]
      [LocallyCompactSpace (GeneralLinear n E.Carrier)]
      [TotallyDisconnectedSpace (GeneralLinear n E.Carrier)]
      [MeasurableSpace (GeneralLinear n E.Carrier)] [BorelSpace (GeneralLinear n E.Carrier)]
      (μ : Measure (GeneralLinear n E.Carrier)) [IsFiniteMeasureOnCompacts μ]
      [μ.IsMulLeftInvariant]
      (A : ∀ i, SigmaIntertwiner σ (t.shape.size i) (t.blocks i).representation),
      twistedDistribution μ t.standardModule.representation (temperedStandard_isAdmissible T t)
        (temperedStandardSigmaIntertwiner T hModule σ t A).toLinearMap ∈
        sigmaProperInducedSpan.{u,v,z} σ μ := by
  let := T.topology
  let := T.localField
  let := T.valuativeRel
  let := hModule
  intro _ _ _ _ _ μ _ _ A
  let B := t.shape
  let R (i : Fin B.length) := (T.twistedBlocks B t.blocks t.exponent i).representation
  let C (i : Fin B.length) : SigmaIntertwiner σ (B.size i) (R i) :=
    twistTwistedIntertwiner (entrywiseAut σ (B.size i))
      (T.determinantPowerCharacter (B.size i) (t.exponent i))
      (determinantPowerCharacter_entrywiseAut T hModule σ _ _) (A i)
  let Ξ := B.blockTensor R
  let κ := T.leviHalfModulus B
  have hκ (m : B.Levi E.Carrier) : κ (leviAut σ B m) = κ m := by
    apply Units.ext
    have hm : T.leviModulus B (leviAut σ B m) = T.leviModulus B m :=
      leviModulus_leviAut σ B m
    dsimp only [κ]
    rw [leviHalfModulus_apply, leviHalfModulus_apply, hm]
  let Ξ' := twist κ Ξ
  let A' := twistTwistedIntertwiner (leviAut σ B) κ hκ (leviTensorIntertwiner σ B C)
  have hR (i : Fin B.length) : IsAdmissible (R i) :=
    (RegularHeadExistence.twistedBlock_admissible_finiteLength T t i).1
  let (i : Fin B.length) : (R i).IsIrreducible :=
    RegularHeadExistence.twistedBlock_irreducible T t i
  have hΞ : IsAdmissible Ξ := FiniteTensor.isAdmissible_external R hR
  have hΞirr : Ξ.IsIrreducible := FiniteTensor.isIrreducible_external R
    (fun i f => (admissibleSchur_scalarEndomorphism _ (hR i) inferInstance f).exists)
  have hΞ' : IsAdmissible Ξ' :=
    (isAdmissible_twist_iff κ Ξ (T.isOpen_ker_leviHalfModulus B)).mpr hΞ
  have hΞ'irr : Ξ'.IsIrreducible := (isIrreducible_twist_iff κ Ξ).mpr hΞirr
  let (i : Fin B.length) : SecondCountableTopology (GeneralLinear (B.size i) E.Carrier) :=
    T.generalLinearSecondCountableTopology _
  let : SecondCountableTopology (B.Levi E.Carrier) := inferInstanceAs
    (SecondCountableTopology (∀ i : Fin B.length, GeneralLinear (B.size i) E.Carrier))
  have hI : IsAdmissible (Induction.smoothInduced (B.parabolic E.Carrier)
      (Ξ'.comp (B.leviProjection E.Carrier))) := temperedStandard_isAdmissible T t
  have hTrace := twistedDistribution_mem_sigmaProperInducedSpan_of_separable.{u,v,z,w}
    σ μ B ht Ξ' hΞ' hΞ'irr A' hI
  exact hTrace

/-- Determinant powers of this local field are trivial on compact subgroups. -/
theorem determinantPowerCharacter_isUnramified (r : ℕ) (s : ℝ) :
    letI := T.topology
    IsUnramifiedCharacter (T.determinantPowerCharacter r s) := by
  let := T.topology
  intro C hC g hg
  change (positiveUnitsToComplex.comp (Units.map (NNReal.rpowMonoidHom s)))
      (T.determinantNorm r g) = 1
  rw [T.determinantNorm_eq_one_of_mem_compact r C hC g hg, map_one]

omit [TopologicalSpace F] in
private theorem reindex_symm_entrywiseAut {a b : ℕ} (h : a = b) (g : GeneralLinear b E.Carrier) :
    (GeneralLinear.reindex (R := E.Carrier) (finCongr h)).symm (entrywiseAut σ b g) =
      entrywiseAut σ a ((GeneralLinear.reindex (R := E.Carrier) (finCongr h)).symm g) := by
  subst b
  ext i j
  rfl

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
include hModule in
/-- A one-block standard module is irreducible and becomes tempered after an invariant unramified
twist. The rank transport is the literal singleton-block reindexing. -/
theorem singleBlockStandard_irreducible_essentiallyTempered (ht : t.shape.length = 1) :
    letI := T.topology
    t.standardModule.IsIrreducible ∧
      ∃ ψ : GeneralLinear n E.Carrier →* ℂˣ, IsUnramifiedCharacter ψ ∧
        (∀ g, ψ (entrywiseAut σ n g) = ψ g) ∧
        IsTemperedRep (twist ψ t.standardModule.representation) := by
  let := T.topology
  let := T.localField
  let := T.valuativeRel
  let := hModule
  let B := t.shape
  let i : Fin B.length := B.singleBlockIndex ht
  let heq := B.singleBlock_size ht i
  let r : GeneralLinear n E.Carrier ≃ₜ* GeneralLinear (B.size i) E.Carrier :=
    { toMulEquiv := (GeneralLinear.reindex (R := E.Carrier) (finCongr heq)).symm
      continuous_toFun := continuous_reindex_finCongr_symm heq
      continuous_invFun := continuous_reindex_finCongr heq }
  let R (j : Fin B.length) := (T.twistedBlocks B t.blocks t.exponent j).representation
  have hR (j : Fin B.length) : IsSmooth (R j) := (T.twistedBlocks B t.blocks t.exponent j).isSmooth
  let e := T.singleBlockNormalizedProductEquiv B ht R hR i
  have hEirr : Representation.IsIrreducible ((R i).comp r.toMonoidHom) :=
    (isIrreducible_comp_continuousMulEquiv_iff _ r).mpr
      (RegularHeadExistence.twistedBlock_irreducible T t i)
  refine ⟨LengthTwo.isIrreducible_of_equiv e.symm hEirr, ?_⟩
  let χ := (T.determinantPowerCharacter (B.size i) (t.exponent i)).comp r.toMonoidHom
  have hχ : IsUnramifiedCharacter χ :=
    (determinantPowerCharacter_isUnramified T (B.size i) (t.exponent i)).comp_of_continuous
      r.toMonoidHom r.continuous
  have hχσ (g : GeneralLinear n E.Carrier) : χ (entrywiseAut σ n g) = χ g := by
    change T.determinantPowerCharacter (B.size i) (t.exponent i)
      ((GeneralLinear.reindex (R := E.Carrier) (finCongr heq)).symm (entrywiseAut σ n g)) =
      T.determinantPowerCharacter (B.size i) (t.exponent i) (r g)
    rw [reindex_symm_entrywiseAut σ heq]
    exact determinantPowerCharacter_entrywiseAut T hModule σ _ _ (r g)
  refine ⟨χ⁻¹, hχ.inv, fun g => congrArg Inv.inv (hχσ g), ?_⟩
  let P := (t.blocks i).representation.comp r.toMonoidHom
  have hP : IsTemperedRep P := by
    let G := GeneralLinear n E.Carrier
    let H := GeneralLinear (B.size i) E.Carrier
    let _: MeasurableSpace (G ⧸ Subgroup.center G) := borel _
    have _: BorelSpace (G ⧸ Subgroup.center G) := ⟨rfl⟩
    let _: MeasurableSpace (H ⧸ Subgroup.center H) := borel _
    have _: BorelSpace (H ⧸ Subgroup.center H) := ⟨rfl⟩
    have ht := (isTemperedRep_iff_isTempered T (t.blocks i).representation).mpr (t.tempered i)
    intro μ _
    exact isTemperedModCenter_comp_continuousMulEquiv (t.blocks i).representation r μ (ht _)
  let e' : t.standardModule.representation.Equiv (twist χ P) := e
  have e'' : (twist χ⁻¹ t.standardModule.representation).Equiv P := by
    have e₀ := twistEquiv χ⁻¹ e'
    rwa [twist_inv_twist] at e₀
  exact (isTemperedRep_iff_of_equiv e'').mpr hP

end Langlands.BaseChange
