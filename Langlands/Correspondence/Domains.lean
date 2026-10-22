import Langlands.Weil.Local.Parameters
import Langlands.WeilDeligne.ParameterRelations
import Langlands.Correspondence.SupercuspidalRelations

/-!
# Actual domains and structural conditions for correspondence families

The parameter domains are the published local Weil and Weil–Deligne class
spaces of the constructed local Weil group. The bijection propositions below
are components of the correspondence, not the normalized LLC itself.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Actual local Frobenius-semisimple WD classes, allowing nonzero monodromy. -/
abbrev WeilDeligneClass (n : ℕ+) :=
  Weil.Local.LocalFrobeniusSemisimpleParameterClassesOfRank.{uF, uP} F (n : ℕ)

/-- Continuous irreducible representations of the actual local Weil group. -/
abbrev IrreducibleWeilClass (n : ℕ+) :=
  Weil.Local.LocalContinuousIrreducibleWeilClasses.{uF, uP} F (n : ℕ)

/-- The underlying genuine pair class of a parameter class. -/
abbrev parameterForget {n : ℕ+} (D : WeilDeligneClass.{uF, uP} F n) :
    WeilDeligneRepresentation.IsomorphismClasses.{0, uF, uP} ℂ
      (Weil.Local.localWeilGroup F) (Weil.Local.localNormCharacter F).toMonoidHom :=
  WeilDeligneRepresentation.ParameterRelations.forget D

/-- The underlying genuine representation class of an irreducible Weil class. -/
abbrev weilClassForget {n : ℕ+} (σ : IrreducibleWeilClass.{uF, uP} F n) :
    FiniteRepresentation.IsomorphismClasses.{0, uF, uP} ℂ (Weil.Local.localWeilGroup F) :=
  FiniteRepresentation.forgetPropertyClass
    (fun A : Weil.Local.LocalWeilRepresentation.{uF, uP} F =>
      A.IsContinuous ∧ A.IsIrreducible) σ.val

-- The result sort joins universe levels; the body must retain distinct carriers.
set_option linter.checkUnivs false in
/-- Maps at all positive ranks on the full actual class spaces. -/
abbrev FullMap :=
  (n : ℕ+) → WeilDeligneClass.{uF, uP} F n → AutomorphicClass.{uF, uA} F n

set_option linter.checkUnivs false in
/-- The irreducible-Weil/supercuspidal family has different domains. -/
abbrev SupercuspidalMap :=
  (n : ℕ+) → IrreducibleWeilClass.{uF, uP} F n →
    SupercuspidalAutomorphicClass.{uF, uA} F n

/-- The disjoint union of all positive-rank full parameter classes. -/
abbrev TotalParameterClass := Σ n : ℕ+, WeilDeligneClass.{uF, uP} F n

/-- The disjoint union of automorphic classes over all positive matrix ranks. -/
abbrev TotalAutomorphicClass := Σ n : ℕ+, AutomorphicClass.{uF, uA} F n

/-- The actual descended vector-space dimension of a parameter class. -/
def parameterDimension (D : TotalParameterClass.{uF, uP} F) : ℕ :=
  WeilDeligneRepresentation.classRank (parameterForget F D.2)

/-- The rank certificate is inherited from the actual quotient's dimension. -/
theorem parameterDimension_eq_rank (D : TotalParameterClass.{uF, uP} F) :
    parameterDimension F D = (D.1 : ℕ) :=
  D.2.property

/-- A rank-indexed family induces a map on the disjoint unions. -/
def fullTotalMap (c : FullMap.{uF, uP, uA} F) :
    TotalParameterClass.{uF, uP} F → TotalAutomorphicClass.{uF, uA} F :=
  fun D => ⟨D.1, c D.1 D.2⟩

/-- The target GL rank equals the source parameter's vector-space dimension. -/
def PreservesRank (c : FullMap.{uF, uP, uA} F) : Prop :=
  ∀ D, ((fullTotalMap F c D).1 : ℕ) = parameterDimension F D

/-- This scope condition follows intrinsically from the rank-indexed types. -/
theorem fullMap_preservesRank (c : FullMap.{uF, uP, uA} F) :
    PreservesRank F c := by
  intro D
  exact (parameterDimension_eq_rank F D).symm

/-- Exhaustion and uniqueness of preimages at every positive rank. -/
def RankwiseBijective (c : FullMap.{uF, uP, uA} F) : Prop :=
  ∀ n, Function.Bijective (c n)

/-- Bijectivity for the separate irreducible-Weil/supercuspidal family. -/
def SupercuspidalRankwiseBijective (c : SupercuspidalMap.{uF, uP, uA} F) : Prop :=
  ∀ n, Function.Bijective (c n)

/-- Equality of families is pointwise equality on the genuine class spaces. -/
theorem fullMap_ext {c d : FullMap.{uF, uP, uA} F}
    (h : ∀ n D, c n D = d n D) : c = d := by
  funext n D
  exact h n D

/-- The full parameter class is the actual zero-monodromy pair of the Weil class.
This relation does not assume the continuity/open-inertia or semisimplicity bridge. -/
def IsZeroMonodromyOf {n : ℕ+}
    (σ : IrreducibleWeilClass.{uF, uP} F n)
    (D : WeilDeligneClass.{uF, uP} F n) : Prop :=
  ∃ A : Weil.Local.LocalWeilRepresentation.{uF, uP} F,
    FiniteRepresentation.classOf A = weilClassForget F σ ∧
      WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy
            (Weil.Local.localNormCharacter F).toMonoidHom A) =
        parameterForget F D

/-- Extension includes existence of the zero-monodromy image in the full domain. -/
def ExtendsSupercuspidal (c0 : SupercuspidalMap.{uF, uP, uA} F)
    (c : FullMap.{uF, uP, uA} F) : Prop :=
  ∀ n σ, ∃ D : WeilDeligneClass.{uF, uP} F n,
    IsZeroMonodromyOf F σ D ∧
      c n D = supercuspidalToAutomorphic F (c0 n σ)

-- The family result sort joins all three levels, which remain separate in its body.
set_option linter.checkUnivs false in
/-- One full rank-indexed family for every prime and actual finite p-adic extension. -/
abbrev FullFamily :=
  (p : ℕ) → [Fact p.Prime] → (F : PadicField.{uF} p) → FullMap.{uF, uP, uA} F

set_option linter.checkUnivs false in
/-- One supercuspidal family over all actual fields and positive ranks. -/
abbrev SupercuspidalFamily :=
  (p : ℕ) → [Fact p.Prime] → (F : PadicField.{uF} p) →
    SupercuspidalMap.{uF, uP, uA} F

end Langlands.Correspondence
