import Langlands.AllField.Representation.RankinSelberg.TemperedTypeDatum
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.RankinSelberg.LocalFactor
import Langlands.Representation.Shahidi.Induction
import Mathlib.Algebra.Module.ULift

/-!
# Three results of JPSS 1983, Section 9, over a nonarchimedean local field

Each proposition is stated for one nonarchimedean local field `F`, given by its
instances.

* `GenericStandardModuleStatement F`: the Langlands classification of generic
  representations with the identification of Whittaker models used in JPSS 1983, (9.4),
  printed page 458: a generic irreducible representation `π` has the Whittaker
  functions of the standard module `ξ` of a datum of tempered blocks with antitone
  real exponents.
* `TemperedPoleBoundStatement F`: the pole bound of JPSS 1983, (8.4), printed pages
  451-452: for irreducible tempered `τ` and `σ`, `L(s, τ × σ)` has no pole in
  `Re s > 0`.
* `InducedTailLFactorAt F`: JPSS 1983, (9.3), printed pages 455-457, in the form of the
  Library's `RankinSelberg.InducedTailLFactorStatement`: the L-polynomial of the second
  block against `σ` divides that of the two-block induction against `σ`.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg (whittakerSet inverseWhittakerSet IsOfWhittakerType)
open Langlands.AllField.RankinSelberg

open _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV uV₁ uV₂ uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]

/-- JPSS 1983, (9.4), printed page 458, the paragraph of display (4), with the
Langlands classification it uses. Every irreducible admissible generic
representation `π` of `GL_(r+1)(F)` has, for its character `ψ`, the `ψ`- and
`ψ̄`-Whittaker functions of the standard module `ξ = Ind(τ_1 ν^(u_1), …, τ_m ν^(u_m))`
of a datum `d` of irreducible tempered blocks of Whittaker type with
`u_1 ≥ ⋯ ≥ u_m`. -/
def GenericStandardModuleStatement : Prop :=
  ∀ (ψ : UnitaryAdditiveCharacter F) (r : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V),
    IsGeneric ψ r π →
    ∃ d : TemperedTypeDatum.{uF, max uF uV} (F := F) (r + 1),
      whittakerSet ψ r d.standardModule = whittakerSet ψ r π ∧
        inverseWhittakerSet ψ r d.standardModule = inverseWhittakerSet ψ r π

/-- JPSS 1983, (8.4), printed pages 451-452, the pole bound: for irreducible tempered
`τ` of `GL_(r+1)(F)` and `σ` of `GL_(t+1)(F)`, every certified L-polynomial `P` of
the pair, `L(s, τ × σ) = P(q^(-s))⁻¹`, has no zero in the open unit disk; that is,
`L(s, τ × σ)` has no pole in `Re s > 0`. -/
def TemperedPoleBoundStatement : Prop :=
  ∀ (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (GeneralLinear (t + 1) F) W),
    Representation.IsIrreducible τ → IsTemperedRepresentation τ →
    Representation.IsIrreducible σ → IsTemperedRepresentation σ →
    ∀ P : ℂ[X], IsPadicSymmetricLPolynomial F ψ ν.val τ σ P →
      ∀ w : ℂ, ‖w‖ < 1 → P.eval w ≠ 0

/-- JPSS 1983, Lemma (9.3), printed pages 455-457, in the form of
`RankinSelberg.InducedTailLFactorStatement` with the field `F`: for `π₁`, `π₂` and
`σ` of Whittaker type, the L-polynomial of `(π₂, σ)` divides that of the normalized
upper two-block induction `Ind(π₁, π₂)` against `σ`; both exist. The block carriers
are lifted to a common universe to form the block family. -/
def InducedTailLFactorAt : Prop :=
  ∀ (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (a b t : ℕ)
    {V₁ : Type uV₁} [AddCommGroup V₁] [Module ℂ V₁]
    {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GeneralLinear (a + 1) F) V₁)
    (π₂ : Representation ℂ (GeneralLinear (b + 1) F) V₂)
    (σ : Representation ℂ (GeneralLinear (t + 1) F) W),
    IsOfWhittakerType a (standardCharacter ψ a) π₁ →
    IsOfWhittakerType b (standardCharacter ψ b) π₂ →
    IsOfWhittakerType t (standardCharacter ψ t) σ →
    let π₁' : Representation ℂ (GeneralLinear (a + 1) F) (ULift.{uV₂} V₁) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₁
    let π₂' : Representation ℂ (GeneralLinear (b + 1) F) (ULift.{uV₁} V₂) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₂
    ∃ Pfull Ptail : ℂ[X],
      IsPadicSymmetricLPolynomial F ψ ν.val
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced
          (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
          (Shahidi.pairFamily π₁' π₂')) σ Pfull ∧
      IsPadicSymmetricLPolynomial F ψ ν.val π₂ σ Ptail ∧
      Ptail ∣ Pfull

end Langlands.AllField.RankinSelberg
