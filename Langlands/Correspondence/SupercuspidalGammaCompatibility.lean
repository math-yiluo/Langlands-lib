import Langlands.Correspondence.SupercuspidalFactorCompatibility
import Langlands.Representation.RankinSelberg.PairFactors

/-!
# Derived gamma compatibility of supercuspidal families

The arithmetic pair gamma factor is `ε(s) L(1 - s, (X ⊗ Y)^∨) / L(s, X ⊗ Y)`,
built from the arithmetic epsilon relation and the published reflected L-ratio.
The Rankin-Selberg side is the published symmetric JPSS gamma relation, lifted to
supercuspidal classes. The derivation from the L, epsilon and dual conditions is
stated as a proposition only.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA uV uW

open LocalFactor LocalFactor.CommonClosure Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The unit `q⁻¹` for the canonical residue cardinality `q`: the reflection
`X ↦ q⁻¹ / X` corresponds to `s ↦ 1 - s` at `X = q^(-s)`. -/
def residueReflection : ℂˣ :=
  WeilDeligne.reflectionScale (F.canonicalTopologicalData.residueCardinality : ℝ)
    (by exact_mod_cast Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one)

/-- `γ(s, X ⊗ Y, ψ) = G(q^(-s))` for the supplied system: for some `c q^(-ms)` that
is the arithmetic epsilon factor, `G` is `c X^m L((X ⊗ Y)^∨)(q⁻¹/X) / L(X ⊗ Y)(X)`. -/
def IsArithmeticPairGammaFactor (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F) (X Y : LocalPairClass.{uF, uP} F)
    (G : RatFunc ℂ) : Prop :=
  ∃ (c : ℂˣ) (m : ℤ), IsArithmeticPairEpsilonFactor F eC ε hε ψ X Y c m ∧
    G = (RankinSelberg.rationalEpsilonMonomial c m : RatFunc ℂ) *
      WeilDeligne.rationalLRatioClass (localInertia F) (localGeometricFrobenius F)
        (residueReflection F) (WeilDeligneRepresentation.tensorClass X Y)

/-- `γ(s, π × τ, ψ) = G(q^(-s))` for supercuspidal classes of ranks `r + 1` and
`n + 1`, in either rank order: the published symmetric JPSS gamma relation on
representatives. Representation equivalences preserve it. -/
def IsSupercuspidalPairGammaFactor (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalAdditiveHaarMeasure F) {r n : ℕ}
    (π : PadicField.SupercuspidalClass.{uV, uF} F (r + 1) (Nat.succ_pos r))
    (τ : PadicField.SupercuspidalClass.{uW, uF} F (n + 1) (Nat.succ_pos n))
    (G : RatFunc ℂ) : Prop :=
  letI := F.canonicalTopologicalData.topology
  Quotient.lift₂
    (fun (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r + 1))
        (B : GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := n + 1)) =>
      RankinSelberg.IsPadicSymmetricGammaFactor F ψ ν
        A.obj.representation B.obj.representation G)
    (by
      rintro A B A' B' ⟨i⟩ ⟨j⟩
      exact propext (RankinSelberg.IsPadicSymmetricGammaFactor.congr_equiv
        (SmoothRep.equivOfIso (GeneralLinear.supercuspidalProperty.ι.mapIso i))
        (SmoothRep.equivOfIso (GeneralLinear.supercuspidalProperty.ι.mapIso j))))
    π τ

/-- Pair gamma compatibility of a supercuspidal map for the supplied system: for
every nontrivial `ψ`, all ranks and all irreducible Weil classes `σ`, `τ`, a
self-dual measure exists, and for every self-dual measure some `G` is both the
JPSS gamma factor of the image pair and the arithmetic gamma factor of `σ ⊗ τ`. -/
def SupercuspidalPairGammaCompatibility (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uP} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (c : SupercuspidalMap.{uF, uP, uA} F) : Prop :=
  ∀ (ψ : NontrivialAdditiveCharacter F) (r n : ℕ)
    (σ : IrreducibleWeilClass.{uF, uP} F r.succPNat)
    (τ : IrreducibleWeilClass.{uF, uP} F n.succPNat),
    (∃ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν) ∧
    ∀ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν →
      ∃ G : RatFunc ℂ,
        IsSupercuspidalPairGammaFactor F ψ ν (c r.succPNat σ) (c n.succPNat τ) G ∧
          IsArithmeticPairGammaFactor F eC ε hε ψ (weilPairClass F σ) (weilPairClass F τ) G

/-- Gamma compatibility relative to a rank-one reciprocity candidate: some system
with base reciprocity component `e` satisfies `SupercuspidalPairGammaCompatibility`. -/
def SupercuspidalGammaCompatibility (e : ReciprocityCandidate F)
    (c : SupercuspidalMap.{uF, uP, uA} F) : Prop :=
  ∃ (eC : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uP} F)
    (hε : NonabelianSystem.IsSystem F eC ε),
    IsBaseReciprocity F e eC ∧ SupercuspidalPairGammaCompatibility F eC ε hε c

/-- Derived gamma compatibility (statement only): for every system and every
supercuspidal map, the pair L/epsilon conditions and dual compatibility imply
the pair gamma condition for the same system and the same map. -/
def SupercuspidalGammaFromFactorsStatement : Prop :=
  ∀ (eC : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uP} F)
    (hε : NonabelianSystem.IsSystem F eC ε) (c : SupercuspidalMap.{uF, uP, uA} F),
    SupercuspidalPairFactorCompatibility F eC ε hε c →
      SupercuspidalDualCompatibility F c →
        SupercuspidalPairGammaCompatibility F eC ε hε c

end Langlands.Correspondence
