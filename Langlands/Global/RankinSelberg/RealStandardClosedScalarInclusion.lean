import Langlands.Global.RankinSelberg.RealStandardCompactFinite
import Langlands.Representation.Archimedean.RealBlockPositionData
import Langlands.Representation.Archimedean.RealStandardCompactWindow
import Langlands.Representation.Archimedean.RealPrincipalSeriesCompactAverages
import Langlands.Representation.Archimedean.SmoothHilbertTransposePairingReduction
import Langlands.Representation.Archimedean.SmoothIntertwiner

/-! # Closed smooth inclusion from a real standard module to its position series -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean Topology
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

open DerivativeSmoothVectors RealPrincipalSeriesHilbert RealStandardCompactWindow

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

local notation "G" n:max => Langlands.GeneralLinear n ℝ
local notation "K" n:max => unitaryCompact ℝ n
local notation "O" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "I" n:max => matrixModel ℝ n
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "S" n:max ds:max => realStandardModule n ds
local notation "P" rank:max ds:max => RealStandardCompactBanach.representation (n := rank) ds
local notation "D" n:max ds:max => DerivativeSmoothVectors (I n) (P n ds)
local notation:max "ε" n:max ds:max => derivativeCLM (I n) (P n ds) []

/-- The rank-one characters at the original positions of a real standard module. -/
def positionCharacters (n : ℕ) (ds : List RealBlock) : List RealCharacterData :=
  List.ofFn fun i : Fin n => RealJacquetFrobenius.charData
    (RealBlockPosition.realPositionSign ds i) (GramFormula.realPositionExponent ds i)

theorem length_positionCharacters (n : ℕ) (ds : List RealBlock) :
    (positionCharacters n ds).length = n := List.length_ofFn

theorem principalSeries_positionCharacters (n : ℕ) (ds : List RealBlock) :
    principalSeries ℝ n (realPositionCharacter ((positionCharacters n ds).map RealBlock.character)) =
      principalSeries ℝ n (realPositionCharacter ds) := by
  apply RealBlockPosition.principalSeries_congr
  intro i
  funext x
  rw [RealJacquetFrobenius.realPositionCharacter_map_character _ i (by simp [positionCharacters])]
  dsimp only [positionCharacters]
  rw [List.getElem_ofFn, RealJacquetFrobenius.charData_character_apply,
    RealBlockPosition.realPositionCharacter_eq_charFun]

/-- A real standard module includes as a closed smooth subspace of the scalar
principal series of its position characters, preserving the original functions. -/
def RealStandardClosedScalarInclusionStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    let es := (positionCharacters n ds).map RealBlock.character
    ∃ T : D n ds →L[ℂ] D n es,
      IsClosedEmbedding T ∧
      (∀ g v, T (DerivativeSmoothVectors.representation (I n) (P n ds) g v) =
        DerivativeSmoothVectors.representation (I n) (P n es) g (T v)) ∧
      ∀ v, ((derivativeEquiv es).symm (T v)).val = ((derivativeEquiv ds).symm v).val

set_option maxHeartbeats 1400000 in
theorem realStandardClosedScalarInclusion : RealStandardClosedScalarInclusionStatement := by
  intro n ds hr es
  let X := principalSeries ℝ n (realPositionCharacter ds)
  have hχ : principalSeries ℝ n (realPositionCharacter es) = X := principalSeries_positionCharacters n ds
  have hS : S n es = X := by
    ext f
    rw [mem_realStandardModule_iff, hχ]
    refine ⟨And.left, fun hf => ⟨hf, fun p d hd => ?_⟩⟩
    have he : realInducedBlockAt es p = none :=
      RealPrincipalSeriesDuality.realInducedBlockAt_map_character (positionCharacters n ds) p
    rw [he] at hd
    cases hd
  have hle : S n ds ≤ S n es := hS.symm ▸ realStandardModule_le_principalSeries n ds
  let i := Submodule.inclusion hle
  have hW : closureSubmodule (n := n) ds ≤ closureSubmodule es := by
    apply Submodule.topologicalClosure_mono
    rintro _ ⟨f, rfl⟩
    exact ⟨i f, rfl⟩
  let J : Carrier n ds →L[ℂ] Carrier n es :=
    ⟨Submodule.inclusion hW, continuous_subtype_val.subtype_mk _⟩
  have hJ (g : G n) (v : Carrier n ds) : J ((P n ds) g v) = (P n es) g (J v) := by
    have eq := (denseRange_embed ds).equalizer
      (J.continuous.comp ((P n ds) g).continuous) (((P n es) g).continuous.comp J.continuous) (funext fun f => by
        change J ((P n ds) g (embed ds f)) = (P n es) g (J (embed ds f))
        rw [representation_embed, show J (embed ds f) = embed es (i f) from rfl, representation_embed]
        rfl)
    exact congrFun eq v
  let T := SmoothIntertwiner.derivativeMap (I n) (P n ds) (P n es) J hJ
  have hT (f : S n ds) : T (derivativeEquiv ds f) = derivativeEquiv es (i f) := by
    apply (derivativeCLM_nil_injective ℝ n (P n es))
    rw [show (ε n es) (T (derivativeEquiv ds f)) = J ((ε n ds) (derivativeEquiv ds f)) from
      SmoothIntertwiner.derivativeCoordinates_derivativeMapLinear (I n) (P n ds) (P n es)
        J hJ (derivativeEquiv ds f) []]
    simp only [derivativeCLM_apply, iteratedLieDerivative_nil, toSmooth_derivativeEquiv]
    rfl
  have hb : IsEmbedding T := by
    have hJEmb : IsEmbedding J := (show Isometry J from fun _ _ => rfl).isEmbedding
    apply (isEmbedding_derivativeCoordinates (I n) (P n es)).of_comp_iff.mp
    have he : derivativeCoordinates (I n) (P n es) ∘ T =
        (fun f : List (M n) → Carrier n ds => fun w => J (f w)) ∘ derivativeCoordinates (I n) (P n ds) := by
      funext v w
      exact SmoothIntertwiner.derivativeCoordinates_derivativeMapLinear (I n) (P n ds) (P n es) J hJ v w
    rw [he]
    exact (IsEmbedding.piMap fun _ => hJEmb).comp (isEmbedding_derivativeCoordinates (I n) (P n ds))
  let : TopologicalSpace X := compactRestrictionTopology n ds
  let F (v : D n es) : X := ⟨((derivativeEquiv es).symm v).val, hS ▸ ((derivativeEquiv es).symm v).prop⟩
  have hF : Continuous F := by
    apply continuous_induced_rng.mpr
    let c : C(K n, O n) := ⟨(orthogonalCompactEquiv n).symm, continuous_orthogonalCompactEquiv_symm⟩
    have he (v : D n es) : restrict n ds (F v) = ((ε n es) v).val.comp c := by
      obtain ⟨f, rfl⟩ := (derivativeEquiv es).surjective v
      ext k
      have hk : Unitary.toUnits (c k) = k.val := congrArg Subtype.val
        ((orthogonalCompactEquiv n).apply_symm_apply k)
      simp only [restrict, F, LinearEquiv.symm_apply_apply]
      change f.val k.val = (((ε n es) (derivativeEquiv es f)).val) (c k)
      rw [derivativeCLM_apply, iteratedLieDerivative_nil, toSmooth_derivativeEquiv, embed_val,
        compactRestriction_apply, hk]
    change Continuous (fun v => restrict n ds (F v))
    simp_rw [he]
    exact (ContinuousMap.compCLM ℂ ℂ c).continuous.comp (continuous_subtype_val.comp (ε n es).continuous)
  have hRange : Set.range T = F ⁻¹' {f : X | f.val ∈ S n ds} := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨f, rfl⟩ := (derivativeEquiv ds).surjective w
      change ((derivativeEquiv es).symm (T (derivativeEquiv ds f))).val ∈ S n ds
      rw [hT, LinearEquiv.symm_apply_apply]
      exact f.prop
    · intro hv
      let f : S n ds := ⟨((derivativeEquiv es).symm v).val, hv⟩
      refine ⟨derivativeEquiv ds f, (hT f).trans ?_⟩
      exact (congrArg (derivativeEquiv es) (Subtype.ext rfl)).trans ((derivativeEquiv es).apply_symm_apply v)
  have hClosed : IsClosed (Set.range T) := by
    rw [hRange]
    exact (realStandardCompactClosed n ds hr).preimage hF
  refine ⟨T, ⟨hb, hClosed⟩, fun g v => ?_, fun v => ?_⟩
  · obtain ⟨f, rfl⟩ := (derivativeEquiv ds).surjective v
    rw [← derivativeEquiv_translate, hT, hT, ← derivativeEquiv_translate]
    rfl
  · obtain ⟨f, rfl⟩ := (derivativeEquiv ds).surjective v
    rw [hT, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rfl

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
