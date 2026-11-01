import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison
import Langlands.Representation.Derivative.MirabolicProductRestrictionTransport

/-! Compact induction of the actual normalized left identity coefficient. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedOrbit
  GeneralLinear.Mirabolic.MixedProduct HarmonicAnalysis Induction
  Jacquet.Localization MixedProductTensor

universe uF uV uW uV' uW'

section RankTransport

variable (k r : ℕ) (R : Type uF) [CommRing R] [TopologicalSpace R]

/-- The actual ambient map from the identity-orbit output rank to the lower
left mixed-product rank. -/
def leftPhiLowerRankEquiv :
    mirabolic (k + r + 1) R ≃ₜ* mirabolic (k + 1 + r) R where
  toMulEquiv := (rankCast (show k + 1 + r = k + r + 1 by omega)).symm
  continuous_toFun := continuous_rankCast_symm _
  continuous_invFun := continuous_rankCast _

/-- The full identity stages section maps onto the actual lower inducing subgroup. -/
theorem leftPhiLowerRank_mem_iff (h : mirabolic (k + r + 1) R) :
    h ∈ (leftStages k r R 1).comap plusSuccessor ↔
      leftPhiLowerRankEquiv k r R h ∈ leftSubgroup (k + 1) r R := by
  rw [leftPhiStages_comap_section]
  exact mem_leftSection_one_iff k r h

/-- The coefficient's section map is exactly restriction of the ambient rank map. -/
theorem leftPhiLowerSectionEquiv_eq
    (l : (leftStages k r R 1).comap plusSuccessor) :
    leftPhiLowerSectionEquiv k r R l =
      ⟨leftPhiLowerRankEquiv k r R l,
        (leftPhiLowerRank_mem_iff k r R l).mp l.property⟩ := by
  apply Subtype.ext
  exact congrArg (rankCast (show k + 1 + r = k + r + 1 by omega)).symm
    (leftPhiStagesSectionEquiv_val k r 1 l)

end RankTransport

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (k r : ℕ) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V)
variable (B : letI := T.topology
  SmoothRep.{0, uF, uW} ℂ (mirabolic (r + 1) F.Carrier))

/-- The published full normalized coefficient comparison intertwines through the
actual ambient rank map, on every quotient element. -/
theorem leftPhiNormalizedSourceEquiv_rank_action
    (l : (leftStages k r F.Carrier 1).comap plusSuccessor)
    (z : letI := T.topology
      leftPhiNormalizedStagesQuotient T k r ρ B.representation ψ 1) :
    letI := T.topology
    leftPhiNormalizedSourceEquiv T k r ψ ρ B
        (leftPhiNormalizedStagesAction T k r ρ B.representation ψ 1 l z) =
      leftPhiSourceCoefficient T k r ψ ρ B
        ⟨leftPhiLowerRankEquiv k r F.Carrier l,
          (leftPhiLowerRank_mem_iff k r F.Carrier l).mp l.property⟩
        (leftPhiNormalizedSourceEquiv T k r ψ ρ B z) := by
  let := T.topology
  have h := Representation.IntertwiningMap.isIntertwining _ _
    (leftPhiNormalizedSourceEquiv T k r ψ ρ B).toIntertwiningMap l z
  change _ = leftPhiSourceCoefficient T k r ψ ρ B
    (leftPhiLowerSectionEquiv k r F.Carrier l) _ at h
  exact h.trans (congrArg
    (fun l => leftPhiSourceCoefficient T k r ψ ρ B l
      (leftPhiNormalizedSourceEquiv T k r ψ ρ B z))
    (leftPhiLowerSectionEquiv_eq k r F.Carrier l))

/-- Compact induction of the entire normalized identity coefficient is the actual
lower mixed-product compact induction, pulled back along its proved rank map. -/
def leftPhiCompactSourceEquiv :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 2)
    letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
    Representation.Equiv
      (compactInduced ((leftStages k r F.Carrier 1).comap plusSuccessor)
        (leftPhiNormalizedStagesAction T k r ρ B.representation ψ 1))
      ((compactInduced (leftSubgroup (k + 1) r F.Carrier)
        (leftPhiSourceCoefficient T k r ψ ρ B)).comp
          (leftPhiLowerRankEquiv k r F.Carrier).toMonoidHom) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 2)
  letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
  (compactInducedTransport (leftPhiLowerRankEquiv k r F.Carrier)
    ((leftStages k r F.Carrier 1).comap plusSuccessor)
    (leftSubgroup (k + 1) r F.Carrier) (leftPhiLowerRank_mem_iff k r F.Carrier)
    (leftPhiNormalizedStagesAction T k r ρ B.representation ψ 1)
    (leftPhiSourceCoefficient T k r ψ ρ B)
    (leftPhiNormalizedSourceEquiv T k r ψ ρ B).toLinearEquiv
    (leftPhiNormalizedSourceEquiv_rank_action T k r ψ ρ B)).symm

@[simp] theorem leftPhiCompactSourceEquiv_eval
    (a : letI := T.topology
      letI := T.generalLinearTopologicalGroup (k + r + 2)
      CompactFunctions ((leftStages k r F.Carrier 1).comap plusSuccessor)
        (leftPhiNormalizedStagesAction T k r ρ B.representation ψ 1))
    (h : mirabolic (k + 1 + r) F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 2)
    letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
    eval (leftSubgroup (k + 1) r F.Carrier) (leftPhiSourceCoefficient T k r ψ ρ B)
        (leftPhiCompactSourceEquiv T k r ψ ρ B a).1 h =
      leftPhiNormalizedSourceEquiv T k r ψ ρ B
        (eval ((leftStages k r F.Carrier 1).comap plusSuccessor)
          (leftPhiNormalizedStagesAction T k r ρ B.representation ψ 1) a.1
          ((leftPhiLowerRankEquiv k r F.Carrier).symm h)) := rfl

variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
variable {ρ' : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V'}
variable {B' : letI := T.topology
  SmoothRep.{0, uF, uW'} ℂ (mirabolic (r + 1) F.Carrier)}

/-- Full compact-function naturality in both actual inputs, with independent
source and target carrier universes. -/
theorem leftPhiCompactSourceEquiv_natural
    (f : ρ.IntertwiningMap ρ') (g : letI := T.topology
      B.representation.IntertwiningMap B'.representation)
    (a : letI := T.topology
      letI := T.generalLinearTopologicalGroup (k + r + 2)
      CompactFunctions ((leftStages k r F.Carrier 1).comap plusSuccessor)
        (leftPhiNormalizedStagesAction T k r ρ B.representation ψ 1)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 2)
    letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
    leftPhiCompactSourceEquiv T k r ψ ρ' B'
        (compactInducedMap ((leftStages k r F.Carrier 1).comap plusSuccessor)
          (leftPhiNormalizedStagesMap T k r ρ B.representation ψ f g 1) a) =
      compactInducedMap (leftSubgroup (k + 1) r F.Carrier)
        (leftPhiSourceCoefficientMap T k r ψ ρ B f g)
        (leftPhiCompactSourceEquiv T k r ψ ρ B a) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 2)
  let := T.generalLinearTopologicalGroup (k + 1 + r + 1)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext h
  exact leftPhiNormalizedSourceEquiv_natural T k r ψ ρ B f g
    (eval ((leftStages k r F.Carrier 1).comap plusSuccessor)
      (leftPhiNormalizedStagesAction T k r ρ B.representation ψ 1) a.1
      ((leftPhiLowerRankEquiv k r F.Carrier).symm h))

end Langlands.Derivative.MirabolicProductMinus
