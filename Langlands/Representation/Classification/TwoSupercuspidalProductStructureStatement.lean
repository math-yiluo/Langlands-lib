import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Tensor.Finite
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Shahidi.TwoBlocks

/-!
# The product of two supercuspidal representations

Zelevinsky 1980, Proposition 1.11. For irreducible supercuspidal
representations `ρ` of `GL_k` and `ρ'` of `GL_l`, the normalized product
`ρ × ρ'` is induced from the standard upper parabolic of block shape `(k, l)`.

(a) If `ρ' ≇ νρ` and `ρ ≇ νρ'`, with `ν = |det|`, then `ρ × ρ'` is irreducible.

(b) If `k = l` and `ρ' ≅ νρ` or `ρ ≅ νρ'`, then `ρ × ρ'` has length two and a
unique nonzero proper invariant subspace `ω`. Both `ω` and `ω' = (ρ × ρ') / ω`
are irreducible, and their normalized `(k, k)` Jacquet modules are isomorphic
to `ρ ⊗ ρ'` and `ρ' ⊗ ρ`, respectively.

These are proposition definitions, not proofs. Ze80 only sketches the
reducibility step of (b).
-/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

section Factors

variable {K : Type uF} [CommRing K] [TopologicalSpace K]

/-- The ordered block factors `(A₀, A₁)` of the standard two-block shape
`(k, l)`: the first block carries `A₀` and the second carries `A₁`. -/
def twoBlockFactors {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (A₀ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k K))
    (A₁ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear l K)) :
    ∀ i : Fin (Shahidi.twoBlocks k l hk hl).length,
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((Shahidi.twoBlocks k l hk hl).size i) K) :=
  Fin.cases A₀ (Fin.cases A₁ finZeroElim)

end Factors

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Ze80 Proposition 1.11(a): if `ρ' ≇ νρ` and `ρ ≇ νρ'`, the normalized product
`ρ × ρ'` of supercuspidal representations of `GL_k` and `GL_l` is irreducible.
The two twist relations compare rank-indexed isomorphism classes, so unequal
ranks are never related. -/
def TwoSupercuspidalNonadjacentProductIrreducible : Prop :=
  letI := T.topology
  ∀ (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (ρ : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (ρ' : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := l)),
    (⟨l, ρ'.isoClass⟩ : Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) ≠
      ⟨k, T.supercuspidalClassRealPowerTwist k 1 ρ.isoClass⟩ →
    (⟨k, ρ.isoClass⟩ : Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) ≠
      ⟨l, T.supercuspidalClassRealPowerTwist l 1 ρ'.isoClass⟩ →
    ((T.normalizedProductInductionFunctor (Shahidi.twoBlocks k l hk hl)).obj
      (twoBlockFactors hk hl ρ.obj ρ'.obj)).IsIrreducible

/-- Ze80 Proposition 1.11(b), composition structure: for supercuspidal `ρ, ρ'`
of `GL_k` with `ρ' ≅ νρ` or `ρ ≅ νρ'`, the normalized product `ρ × ρ'` has a
composition series of length two and exactly one invariant subspace other than
zero and the whole space; that subspace and the quotient by it are irreducible. -/
def TwoSupercuspidalAdjacentProductComposition : Prop :=
  letI := T.topology
  ∀ (k : ℕ) (hk : 0 < k)
    (ρ ρ' : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)),
    (ρ'.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ.isoClass ∨
      ρ.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ'.isoClass) →
    let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
      (twoBlockFactors hk hk ρ.obj ρ'.obj)
    HasCompositionSeriesLength P.obj 2 ∧
      (∃! S : Subrepresentation P.representation, S ≠ ⊥ ∧ S ≠ ⊤) ∧
      ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
        (SmoothRep.subrepresentation P S).IsIrreducible ∧
          (SmoothRep.quotient P S).IsIrreducible

/-- Ze80 Proposition 1.11(b), Jacquet modules: in the adjacent case, for the
invariant subspace `ω` other than zero and the whole space, the normalized
`(k, k)` Jacquet module of `ω` is isomorphic to `ρ ⊗ ρ'`, and that of the
quotient `(ρ × ρ') / ω` is isomorphic to `ρ' ⊗ ρ`. -/
def TwoSupercuspidalAdjacentProductJacquet : Prop :=
  letI := T.topology
  ∀ (k : ℕ) (hk : 0 < k)
    (ρ ρ' : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)),
    (ρ'.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ.isoClass ∨
      ρ.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ'.isoClass) →
    let B := Shahidi.twoBlocks k k hk hk
    let P := (T.normalizedProductInductionFunctor B).obj
      (twoBlockFactors hk hk ρ.obj ρ'.obj)
    ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
      Nonempty (((T.normalizedJacquetFunctor B).obj
          (SmoothRep.subrepresentation P S)).representation.Equiv
        (FiniteTensor.externalSmoothObject
          (twoBlockFactors hk hk ρ.obj ρ'.obj)).representation) ∧
      Nonempty (((T.normalizedJacquetFunctor B).obj
          (SmoothRep.quotient P S)).representation.Equiv
        (FiniteTensor.externalSmoothObject
          (twoBlockFactors hk hk ρ'.obj ρ.obj)).representation)

/-- Ze80 Proposition 1.11: both parts, for the specified field and topology. -/
def TwoSupercuspidalProductStructure : Prop :=
  TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T ∧
    TwoSupercuspidalAdjacentProductComposition.{uF, uV} F T ∧
    TwoSupercuspidalAdjacentProductJacquet.{uF, uV} F T

end Langlands.Classification
