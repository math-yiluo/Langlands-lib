import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionBracketMapStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusCoverReduction
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusBaseChangeProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionEvaluationLinePowers
import Langlands.AlgebraicGeometry.ProjectiveSpace.EvaluationBracketFibres
import Langlands.AlgebraicGeometry.Modules.OpenSectionProducts
import Langlands.AlgebraicGeometry.Modules.BiCech.Kunneth
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent

/-! # Torsion bracket maps from Lefschetz's embedding theorem -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.EvaluationBracket
open Langlands.AlgebraicGeometry.Picard

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n : ℕ}

/-- The reindexing of the frame labels other than the last one. -/
def lastComplEquiv (m : ℕ) : Fin (m + 1) ≃ {j : Fin (m + 2) // j ≠ Fin.last (m + 1)} where
  toFun l := ⟨l.castSucc, Fin.castSucc_ne_last l⟩
  invFun j := j.1.castPred j.2
  left_inv _ := Fin.castPred_castSucc _
  right_inv _ := Subtype.ext (Fin.castSucc_castPred _ _)

/-- A point of a projective frame locus has a bracket chart around it: an open on which the
torsion evaluations at the frame labels other than the last are jointly bijective on sections
over every smaller open, and on which every torsion evaluation line has a generator. -/
theorem Datum.exists_bracketChart [Finite (Fin (2 * g) → ZMod n)] (a : Datum P S g d n)
    {m : ℕ} (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) {x : S} (hx : x ∈ a.frameLocus ρ) :
    ∃ C : Chart (fun r => a.torsionEvaluation r) (m + 1), x ∈ C.W := by
  classical
  have : Fintype (Fin (2 * g) → ZMod n) := Fintype.ofFinite _
  obtain ⟨W0, hW0, hxW0⟩ : ∃ W0 : S.Opens, (∀ k, IsIso ((Scheme.Modules.pullback W0.ι).map
      (a.frameEvaluation ρ k))) ∧ x ∈ W0 := TopologicalSpace.Opens.mem_sSup.mp hx
  have hiso : IsIso ((Scheme.Modules.pullback W0.ι).map
      (a.frameEvaluation ρ (Fin.last (m + 1)))) := hW0 (Fin.last (m + 1))
  have hbij0 : ∀ V : S.Opens, V ≤ W0 → Function.Bijective
      (fun (s : Γ(a.rigidificationModule, V)) (j : {j : Fin (m + 2) // j ≠ Fin.last (m + 1)}) =>
        (a.torsionEvaluation (ρ j)).app V s) := fun V hV =>
    Langlands.AlgebraicGeometry.Modules.OpenSectionProducts.bijective_pi_app_of_isIso_pullback
      (fun j : {j : Fin (m + 2) // j ≠ Fin.last (m + 1)} => a.torsionEvaluation (ρ j)) W0 hiso hV
  have hfr : ∀ r : Fin (2 * g) → ZMod n, ∃ (T : S.Opens) (_ : x ∈ T)
      (e : Γ((Scheme.Modules.pullback (a.torsionPoint r)).obj a.cubicBundle.obj, T)),
      Scheme.Modules.IsFrameOn e T := fun r =>
    Langlands.AlgebraicGeometry.Modules.BiCech.exists_isFrameOn_of_isLocallyFreeRankOne
      (a.torsionEvaluationLine r).property x
  choose T hxT e he using hfr
  let W : S.Opens := W0 ⊓ Finset.univ.inf T
  have hWT : ∀ r, W ≤ T r := fun r =>
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ r))
  have hxW : x ∈ W := by
    exact ⟨hxW0, Finset.inf_induction (p := fun U : S.Opens => x ∈ U) trivial
      (fun _ h₁ _ h₂ => ⟨h₁, h₂⟩) (fun r _ => hxT r)⟩
  refine ⟨{ ρ := fun l => ρ l.castSucc
            W := W
            q := fun r => ((Scheme.Modules.pullback (a.torsionPoint r)).obj
              a.cubicBundle.obj).presheaf.map (homOfLE (hWT r)).op (e r)
            isFrame := fun r => ((he r).map (homOfLE (hWT r))).mono (hWT r)
            bij := fun V hV => ?_ }, hxW⟩
  have h0 := hbij0 V (hV.trans inf_le_left)
  have he' := (Equiv.piCongrLeft' (fun j : {j : Fin (m + 2) // j ≠ Fin.last (m + 1)} =>
    Γ((Scheme.Modules.pullback (a.torsionPoint (ρ j))).obj a.cubicBundle.obj, V))
    (lastComplEquiv m).symm).bijective
  exact he'.comp h0

/-- The pullbacks of a datum to the field-valued points of its base, with the published
base-change comparisons of the cubic direct image and of the torsion evaluations. -/
def Datum.fieldModel [IsLocallyNoetherian S] (hd : 0 < d) (a : Datum P S g d n)
    {K : Type u} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) :
    FieldModel (fun r => a.torsionEvaluation r) (cubicProjectiveDimension g d + 1) t where
  E' := (a.pullback t).rigidificationModule
  Q' r := (Scheme.Modules.pullback ((a.pullback t).torsionPoint r)).obj
    (a.pullback t).cubicBundle.obj
  ev' r := (a.pullback t).torsionEvaluation r
  α := @asIso _ _ _ _ (a.rigidificationBaseChangeMap t) ((cubicDirectImage P S g d n hd a).2 _ t)
  β r := a.torsionEvaluationBaseChangeIso t r
  comm r := a.rigidificationBaseChangeMap_comp_torsionEvaluation t r
  qcE := by
    have := Langlands.AlgebraicGeometry.Modules.isFinitePresentation_of_hasFiniteLocalBasis _
      (hasFiniteLocalBasis_of_isLocallyFreeOfRank
        (cubicDirectImage P (Spec (CommRingCat.of K)) g d n hd (a.pullback t)).1)
    infer_instance
  qcQ r := IsLocallyFreeRankOne.isQuasicoherent ((a.pullback t).torsionEvaluationLine r).property
  rankE := (a.pullback t).finrank_cubicSections hd
  rankQ r := finrank_moduleSpecΓ_lineBundle ((a.pullback t).torsionEvaluationLine r)

set_option linter.defProp false in
/-- Proved definition: Lefschetz's embedding theorem for the canonical cubic bundle over
fields implies `TorsionBracketMapStatement`. The bound on the level is the bound of the
published frame-locus cover, and at least one. -/
def torsionBracketMap_of_cubicFieldEmbedding (hL : CubicFieldEmbeddingStatement.{0}) :
    TorsionBracketMapStatement := by
  intro P g d hg hd
  obtain ⟨N, hN⟩ := frameLocusCover_of_cubicFieldEmbedding hL frameLocusBaseChange P g d hg hd
  refine ⟨max N 1, fun n hn T b => ?_⟩
  have hNn : N ≤ n := le_of_max_le_left hn
  have hn1 : 0 < n := le_of_max_le_right hn
  have : NeZero n := ⟨hn1.ne'⟩
  have hcharts : ∀ x : T.obj, ∃ C : Chart (fun r => b.torsionEvaluation r)
      (cubicProjectiveDimension g d + 1), x ∈ C.W := by
    intro x
    obtain ⟨ρ, hρ⟩ := hN n hNn T.obj T.level_isUnit b x
    exact b.exists_bracketChart ρ hρ
  choose chart hchart using hcharts
  have hcov : ∀ x, ∃ i, x ∈ (chart i).W := fun x => ⟨x, hchart x⟩
  let τ : ∀ r, ((Scheme.Modules.pullback (b.torsionPoint r)).obj b.cubicBundle.obj).tensorPow n ≅
      𝟙_ T.obj.Modules := fun r =>
    Langlands.AlgebraicGeometry.Modules.TensorPowerGauge.tensorPowComparison _ n ≪≫
      b.torsionEvaluationLinePowerIso r
  have hcard : 0 < Fintype.card
      (Fin (cubicProjectiveDimension g d + 1) → Fin (2 * g) → ZMod n) := Fintype.card_pos
  let eqv : Fin (Fintype.card
      (Fin (cubicProjectiveDimension g d + 1) → Fin (2 * g) → ZMod n) - 1 + 1) ≃
      (Fin (cubicProjectiveDimension g d + 1) → Fin (2 * g) → ZMod n) :=
    (finCongr (Nat.sub_add_cancel hcard)).trans (Fintype.equivFin _).symm
  refine ⟨_, CoordinateAtlas.atlasMap T.toLocalizationSpec (isAtlas chart hcov τ eqv), ?_⟩
  intro K _ _ y
  obtain ⟨s, hs⟩ := exists_finset_equivalent T.toLocalizationSpec chart hcov hn1 τ eqv
    (fun t => b.fieldModel hd t) y
  exact ⟨s, fun t ht => hs t ht⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
