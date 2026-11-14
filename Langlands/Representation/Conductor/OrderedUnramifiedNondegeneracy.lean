import Langlands.AllFieldBZ.Representation.Derivative.OrderedCuspidalProductNondegeneracyStatement
import Langlands.AllFieldBZ.Representation.Derivative.TopLocalizationComparison
import Langlands.Representation.Derivative.LevelCalculus
import Langlands.Representation.Whittaker.EntrywiseCharacter
import Langlands.Representation.Conductor.OrderedUnramifiedRankOneBlocks
import Langlands.Representation.Conductor.OrderedUnramifiedProductComparison

/-!
# Mirabolic nondegeneracy of norm-ordered products of unramified characters

From Bernstein–Zelevinsky's Theorem 4.11 over all nonarchimedean local fields: every
nonzero mirabolic subrepresentation of a normalized product of unramified characters
of `GL_1(F)`, with weakly increasing norms, has nonzero standard Whittaker
coinvariants.
-/

noncomputable section

namespace Langlands.Conductor.OrderedUnramifiedNondegeneracy

open CategoryTheory Langlands.GeneralLinear Langlands.Jacquet.Localization
open Langlands.HarmonicAnalysis
open Langlands.Conductor.OrderedUnramifiedProductComparison
open Langlands.Conductor.OrderedUnramifiedRankOneBlocks

universe uF uV

section Top

variable {F : AllFieldBZ.LocalFieldPackage.{uF}}

/-- Rank transport of a mirabolic representation does not change whether its full upper
coinvariants are nonzero. -/
theorem nontrivial_coinvariants_rankCast (T : F.TopologicalData) (ψ : AddChar F.Carrier ℂ)
    {N M : ℕ} (h : N = M)
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)) :
    letI := T.topology
    Nontrivial (Coinvariants ((AllFieldBZ.Derivative.mirabolicRankCast T h).obj B).representation
        (Mirabolic.upperUnipotent M F.Carrier) (Derivative.TopLocalization.mirabolicUpperCharacter ψ M)) ↔
      Nontrivial (Coinvariants B.representation (Mirabolic.upperUnipotent N F.Carrier)
        (Derivative.TopLocalization.mirabolicUpperCharacter ψ N)) := by
  let := T.topology
  subst h
  rw [AllFieldBZ.Derivative.mirabolicRankCast_refl]
  rfl

/-- A nonzero top derivative of a mirabolic representation gives nonzero full upper
coinvariants for the standard character. -/
theorem nontrivial_coinvariants_of_top (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N : ℕ)
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
    (hk : 0 < N + 1 ∧ N + 1 ≤ N + 1) :
    letI := T.topology
    Nontrivial ((AllFieldBZ.Derivative.mirabolicDerivativeOfOrder T ψ N (N + 1) hk).obj B) →
      Nontrivial (Coinvariants B.representation (Mirabolic.upperUnipotent N F.Carrier)
        ((Langlands.Whittaker.standardCharacter ψ N).comp
          Mirabolic.upperUnipotentEquiv.toMonoidHom)) := by
  let := T.topology
  intro h
  have h2 : Nontrivial ((AllFieldBZ.Derivative.generalLinearRankCast T (Nat.sub_self (N + 1))).obj
      ((AllFieldBZ.Derivative.mirabolicDerivativeOfOrder T ψ N (N + 1) hk).obj B)) := by
    have key : ∀ {a b : ℕ} (e : a = b)
        (A : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear a F.Carrier)),
        Nontrivial A → Nontrivial ((AllFieldBZ.Derivative.generalLinearRankCast T e).obj A) := by
      intro a b e A hA
      subst e
      exact hA
    exact key _ _ h
  have h3 : (AllFieldBZ.Derivative.generalLinearRankCast T (Nat.sub_self (N + 1))).obj
        ((AllFieldBZ.Derivative.mirabolicDerivativeOfOrder T ψ N (N + 1) hk).obj B) =
      (AllFieldBZ.Derivative.mirabolicDerivative T ψ 0 N).obj
        ((AllFieldBZ.Derivative.mirabolicRankCast T (Nat.zero_add N).symm).obj B) :=
    congrArg (fun J => J.obj B) (AllFieldBZ.Derivative.mirabolicDerivativeOfOrder_top T ψ N hk)
  rw [h3] at h2
  have h4 := (Derivative.LevelCalculus.nontrivial_iff_of_iso
    ((AllFieldBZ.Derivative.TopLocalization.mirabolicLocalizationIso T ψ N).app
      ((AllFieldBZ.Derivative.mirabolicRankCast T (Nat.zero_add N).symm).obj B))).2 h2
  have h5 := (nontrivial_coinvariants_rankCast T ψ.complex (Nat.zero_add N).symm B).1 h4
  have hchar : Derivative.TopLocalization.mirabolicUpperCharacter ψ.complex N =
      (Langlands.Whittaker.standardCharacter ψ N).comp
        Mirabolic.upperUnipotentEquiv.toMonoidHom := by
    rw [Derivative.TopLocalization.mirabolicUpperCharacter,
      Langlands.Whittaker.entrywiseCharacter_eq_standardCharacter]
  rw [hchar] at h5
  exact h5

end Top

section Product

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : Fˣ}
  (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)

/-- The normalized product of the rank-one unramified blocks with parameters `z`. -/
abbrev product (n : ℕ) (z : Fin (n + 1) → ℂˣ) :=
  letI := (data F).topology
  ((data F).normalizedProductInductionFunctor.{uF, uF} (blocks n)).obj
    (fun i => (rankOneBlock hϖ (z i)).obj)

/-- **Mirabolic nondegeneracy.** If the norms of `z` are weakly increasing, every nonzero
mirabolic subrepresentation of the normalized product of the rank-one unramified blocks
has nonzero standard Whittaker coinvariants. The input is Bernstein–Zelevinsky's
Theorem 4.11 over all nonarchimedean local fields. -/
theorem nontrivial_coinvariants
    (h411 : AllFieldBZ.Derivative.OrderedCuspidalProductNoDegenerateSubmodules.{uF, uF}
      (pkg F) (data F))
    (n : ℕ) (z : Fin (n + 1) → ℂˣ) (hz : Monotone (fun i => ‖(z i : ℂ)‖))
    (ψ : @UnitaryAdditiveCharacter (pkg F).Carrier _ (data F).topology) :
    letI := (data F).topology
    ∀ U : Subrepresentation
        ((product hϖ n z).representation.comp (mirabolic n (pkg F).Carrier).subtype),
      U ≠ ⊥ →
        Nontrivial (Coinvariants U.toRepresentation (Mirabolic.upperUnipotent n (pkg F).Carrier)
          ((Langlands.Whittaker.standardCharacter ψ n).comp
            Mirabolic.upperUnipotentEquiv.toMonoidHom)) := by
  let := (data F).topology
  intro U hU
  have hA : ∀ i j : Fin (blocks n).length, i < j →
      (⟨(blocks n).size j, (rankOneBlock hϖ (z j)).isoClass⟩ :
          Σ d : ℕ, SupercuspidalClass.{uF, uF} (F := (pkg F).Carrier) (n := d)) ≠
        ⟨(blocks n).size i,
          (data F).supercuspidalClassRealPowerTwist ((blocks n).size i) 1
            (rankOneBlock hϖ (z i)).isoClass⟩ :=
    fun i j hij => rankOneBlock_twist_ne (F := F) hϖ (hz (le_of_lt hij))
  have h := h411 ψ n (blocks n) (fun i => rankOneBlock (F := F) hϖ (z i)) hA U hU
  exact nontrivial_coinvariants_of_top (data F) ψ n _ ⟨Nat.zero_lt_succ n, le_rfl⟩ h

end Product

end Langlands.Conductor.OrderedUnramifiedNondegeneracy
