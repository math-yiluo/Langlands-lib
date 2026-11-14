import Langlands.Representation.Conductor.OrderedUnramifiedRankOneBlocks
import Langlands.Representation.Whittaker.EntrywiseCharacter
import Langlands.Representation.Jacquet.Localization
import Langlands.Group.GL.Mirabolic
import Langlands.AllFieldBZ.Representation.Derivative.FiniteTopLine
import Langlands.AllFieldBZ.Representation.Derivative.TopLocalizationComparison

/-! # The top line of an unramified inducing product -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Conductor.OrderedUnramifiedTopLine

open CategoryTheory GeneralLinear HarmonicAnalysis
open OrderedUnramifiedRankOneBlocks
open Jacquet.Localization

universe uF uV

private def rankCastCarrierEquiv {K : AllFieldBZ.LocalFieldPackage.{uF}}
    (T : K.TopologicalData) {a b : ℕ} (h : a = b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a K.Carrier)) :
    letI := T.topology
    (AllFieldBZ.Derivative.generalLinearRankCast T h).obj A ≃ₗ[ℂ] A := by
  subst b
  exact LinearEquiv.refl ℂ A

/-- The whole upper-character quotient is the entire carrier of the top
derivative, with its terminal rank transport removed. -/
def coinvariantsTopDerivativeEquiv {K : AllFieldBZ.LocalFieldPackage.{uF}}
    (T : K.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter K.Carrier _ T.topology) (m : ℕ)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear m K.Carrier)) :
    letI := T.topology
    Coinvariants A.representation (upperUnipotent m K.Carrier)
      (Whittaker.entrywiseCharacter ψ.complex m) ≃ₗ[ℂ]
        ((AllFieldBZ.Derivative.generalLinearDerivative T ψ m m le_rfl).obj A) := by
  letI := T.topology
  let e := (SmoothRep.equivOfIso
    ((AllFieldBZ.Derivative.TopLocalization.topLocalizationIso T ψ m).app A)).toLinearEquiv
  exact e.trans (rankCastCarrierEquiv T (Nat.sub_self m) _)

variable {F : Type uF} [Field F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem upperUnipotent_rankOne_eq_one (u : upperUnipotent 1 F) : u = 1 := by
  let e := Mirabolic.upperUnipotentEquiv (n := 0) (F := F)
  have h : e.symm u = 1 := Subsingleton.elim _ _
  simpa only [map_one, e.apply_symm_apply] using congrArg e h

private theorem rankOne_relations_eq_bot (w : ℂˣ)
    (θ : upperUnipotent 1 F →* ℂˣ) :
    relations (rankOneBlock hϖ w).obj.representation (upperUnipotent 1 F) θ = ⊥ := by
  rw [eq_bot_iff, relations, Submodule.span_le]
  rintro _ ⟨⟨u, v⟩, rfl⟩
  rw [upperUnipotent_rankOne_eq_one u]
  simp only [OneMemClass.coe_one, map_one, Module.End.one_apply,
    Units.val_one, one_smul, sub_self]
  exact zero_mem _

/-- In rank one the upper group is trivial, so its character quotient is
the original scalar line. -/
def rankOneCoinvariantsLineEquiv (w : ℂˣ)
    (θ : upperUnipotent 1 F →* ℂˣ) :
    Coinvariants (rankOneBlock hϖ w).obj.representation (upperUnipotent 1 F) θ ≃ₗ[ℂ] ℂ :=
  (Submodule.quotEquivOfEqBot _
    (rankOne_relations_eq_bot hϖ w θ)).trans
      (ULift.moduleEquiv : ULift.{uF} ℂ ≃ₗ[ℂ] ℂ)

/-- The whole first derivative of the rank-one block is a complex line. -/
def rankOneTopDerivativeLineEquiv (w : ℂˣ)
    (ψ : letI := (fieldData (F := F)).topology
      UnitaryAdditiveCharacter (AllFieldBZ.LocalFieldPackage.ofField F).Carrier) :
    letI := (fieldData (F := F)).topology
    ((AllFieldBZ.Derivative.generalLinearDerivative (fieldData (F := F))
      ψ 1 1 le_rfl).obj (rankOneBlock hϖ w).obj) ≃ₗ[ℂ] ℂ := by
  letI := (fieldData (F := F)).topology
  exact (coinvariantsTopDerivativeEquiv (fieldData (F := F)) ψ 1
    (rankOneBlock hϖ w).obj).symm.trans
      (rankOneCoinvariantsLineEquiv hϖ w _)

/-- The top derivative of the singleton-block inducing product is a line,
for every ordered tuple of nonzero unramified parameters. -/
def productTopDerivativeLineEquiv (n : ℕ) (z : Fin (n + 1) → ℂˣ)
    (ψ : letI := (fieldData (F := F)).topology
      UnitaryAdditiveCharacter (AllFieldBZ.LocalFieldPackage.ofField F).Carrier) :
    letI := (fieldData (F := F)).topology
    ((AllFieldBZ.Derivative.generalLinearDerivative (fieldData (F := F))
      ψ (n + 1) (n + 1) le_rfl).obj
        (((fieldData (F := F)).normalizedProductInductionFunctor.{uF, uF}
          (BlockShape.singletons (n + 1))).obj
            (fun i => (rankOneBlock hϖ (z i)).obj))) ≃ₗ[ℂ] ℂ :=
  letI := (fieldData (F := F)).topology
  AllFieldBZ.Derivative.finiteProductTopDerivativeLineEquiv.{uF, uF}
    (F := AllFieldBZ.LocalFieldPackage.ofField F)
    (n := n + 1)
    (fieldData (F := F)) ψ (Nat.succ_pos n) (BlockShape.singletons (n + 1))
    (fun i => (rankOneBlock hϖ (z i)).obj)
    (fun i => rankOneTopDerivativeLineEquiv hϖ (z i) ψ)

/-- The standard-character coinvariant space of the unramified inducing
product has dimension one. No norm ordering or irreducibility is assumed. -/
theorem finrank_productCoinvariants (n : ℕ) (z : Fin (n + 1) → ℂˣ)
    (ψ : letI := (fieldData (F := F)).topology
      UnitaryAdditiveCharacter (AllFieldBZ.LocalFieldPackage.ofField F).Carrier) :
    letI := (fieldData (F := F)).topology
    Module.finrank ℂ
      (Coinvariants
        ((((fieldData (F := F)).normalizedProductInductionFunctor.{uF, uF}
          (BlockShape.singletons (n + 1))).obj
            (fun i => (rankOneBlock hϖ (z i)).obj)).representation)
        (upperUnipotent (n + 1) (AllFieldBZ.LocalFieldPackage.ofField F).Carrier)
        (Whittaker.standardCharacter ψ n)) = 1 := by
  let := (fieldData (F := F)).topology
  let e := (coinvariantsTopDerivativeEquiv (fieldData (F := F)) ψ (n + 1)
    (((fieldData (F := F)).normalizedProductInductionFunctor.{uF, uF}
      (BlockShape.singletons (n + 1))).obj
        (fun i => (rankOneBlock hϖ (z i)).obj)))
  let eTop := productTopDerivativeLineEquiv hϖ n z ψ
  rw [← Whittaker.entrywiseCharacter_eq_standardCharacter ψ n]
  exact e.finrank_eq.trans (eTop.finrank_eq.trans (Module.finrank_self ℂ))

end Langlands.Conductor.OrderedUnramifiedTopLine
