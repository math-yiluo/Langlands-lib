import Langlands.Correspondence.FullLFactorCompatibility
import Langlands.Correspondence.AssemblyRelation
import Langlands.Correspondence.SupercuspidalSpecification
import Langlands.WeilDeligne.BlockStatements

/-!
# L-factors of the assembled correspondence

Two statements about the assembly of a supercuspidal correspondence, after
Henniart 2002: the assembly inherits pair L-factor compatibility (Theorem 1.5(iii),
L part), and the assembly is the only full map that extends the supercuspidal
correspondence and has the right L-factors against indecomposable parameters of
smaller rank (Theorem 1.8). These are statements, not proofs.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- `D` is indecomposable: some representative pair is a published indecomposable
Weil–Deligne pair. -/
def IsIndecomposableParameterClass {n : ℕ+} (D : WeilDeligneClass.{uF, uP} F n) : Prop :=
  ∃ A : Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F,
    WeilDeligneRepresentation.classOf A = parameterForget F D ∧
      WeilDeligneRepresentation.Blocks.IsIndecomposable A

/-- `D` is the zero-monodromy class of a continuous irreducible Weil class. -/
def IsIrreducibleWeilParameter {n : ℕ+} (D : WeilDeligneClass.{uF, uP} F n) : Prop :=
  ∃ σ : IrreducibleWeilClass.{uF, uP} F n, IsZeroMonodromyOf F σ D

/-- Inherited pair L-factor compatibility (statement only): the assembly of a
supercuspidal correspondence is compatible with pair L-factors for every
nontrivial additive character. -/
def AssemblyLInheritanceStatement : Prop :=
  ∀ (c0 : SupercuspidalMap.{uF, uP, uA} F) (c : FullMap.{uF, uP, uA} F),
    IsSupercuspidalCorrespondence F c0 → IsAssemblyOf F c0 c → FullPairLCompatibility F c

/-- Characterization of the assembly by L-factors (statement only). Let `c0` be a
supercuspidal correspondence and `ψ` a nontrivial additive character. If a full map
`τ` extends `c0` and, for all ranks `j + 1 < k + 1`, every class `D` of rank `k + 1`
that is not irreducible Weil and every indecomposable class `D'` of rank `j + 1`
satisfy `L(s, τ(D) × τ(D')) = L(s, D ⊗ D')` at `ψ`, then `τ` is the assembly of
`c0`, and every assembly of `c0` equals `τ`. -/
def AssemblyLCharacterizationStatement : Prop :=
  ∀ (c0 : SupercuspidalMap.{uF, uP, uA} F) (τ : FullMap.{uF, uP, uA} F)
    (ψ : NontrivialAdditiveCharacter F),
    IsSupercuspidalCorrespondence F c0 → ExtendsSupercuspidal F c0 τ →
    (∀ k j : ℕ, j < k → ∀ (D : WeilDeligneClass.{uF, uP} F k.succPNat)
        (D' : WeilDeligneClass.{uF, uP} F j.succPNat),
      ¬ IsIrreducibleWeilParameter F D → IsIndecomposableParameterClass F D' →
        IsPairLCompatibleAt F ψ D D' (τ k.succPNat D) (τ j.succPNat D')) →
    IsAssemblyOf F c0 τ ∧ ∀ c : FullMap.{uF, uP, uA} F, IsAssemblyOf F c0 c → c = τ

end Langlands.Correspondence
