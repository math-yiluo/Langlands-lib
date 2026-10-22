import Langlands.WeilDeligne.SpecialBlocks
import Langlands.WeilDeligne.DirectSum
import Langlands.WeilDeligne.Dual
import Langlands.WeilDeligne.Twist
import Langlands.WeilDeligne.Determinant
import Langlands.WeilDeligne.Kernels
import Langlands.WeilDeligne.LinearAlgebraStatements
import Langlands.WeilDeligne.FrobeniusStatements

/-!
# Special blocks: identities, decomposition and classification

Proposition targets for the uncentered blocks `σ ⊗ S_m` of the companion
(`block ν σ m`: weights `ν^j`, raising monodromy, kernel at the top weight).
The block calculus is stated over a general field, with characteristic zero only
for the tensor identities. Decomposition and classification are stated over `ℂ`.
Existence and uniqueness are conclusions; no decomposition is supplied as data.
These are statements, not proofs.
-/

noncomputable section

namespace Langlands.WeilDeligneRepresentation.Blocks

universe uK uG uV uW

/-- A pair is indecomposable when its carrier is nonzero and it has no
decomposition into two nonzero stable subspaces. -/
def IsIndecomposable {G : Type uG} [Group G] {ν : G →* ℂˣ}
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν) : Prop :=
  Nontrivial A ∧
    ∀ S T : Submodule ℂ A, LinearAlgebra.IsStable A S → LinearAlgebra.IsStable A T →
      IsCompl S T → S = ⊥ ∨ T = ⊥

/-- Graded Clebsch–Gordan for special blocks:
`S_m ⊗ S_n ≅ ⨁_{i < min m n} ν^i ⊗ S_{m+n-1-2i}`.
Characteristic zero is needed; the formula fails for `m = n = p` in characteristic `p`. -/
def SpecialBlockTensor : Prop :=
  ∀ (K : Type uK) [Field K] [CharZero K] (G : Type uG) [Group G] (ν : G →* Kˣ) (m n : ℕ),
    Nonempty (WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.tensor (specialBlock ν m) (specialBlock ν n))
      (WeilDeligneRepresentation.directSum fun i : Fin (min m n) =>
        WeilDeligneRepresentation.twist (ν ^ (i : ℕ))
          (specialBlock ν (m + n - 1 - 2 * (i : ℕ)))))

/-- The tensor product of two blocks is the sum of the blocks of the twisted
tensor products of their Weil factors. -/
def BlockTensor : Prop :=
  ∀ (K : Type uK) [Field K] [CharZero K] (G : Type uG) [Group G] (ν : G →* Kˣ)
    (σ : FiniteRepresentation.{uK, uG, uV} K G) (τ : FiniteRepresentation.{uK, uG, uW} K G)
    (m n : ℕ),
    Nonempty (WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.tensor (block ν σ m) (block ν τ n))
      (WeilDeligneRepresentation.directSum fun i : Fin (min m n) =>
        block ν (FiniteRepresentation.twist (ν ^ (i : ℕ)) (FiniteRepresentation.tensor σ τ))
          (m + n - 1 - 2 * (i : ℕ))))

/-- The dual special block: `S_m^∨ ≅ ν^(1-m) ⊗ S_m`, with dual monodromy `-Nᵀ`. -/
def SpecialBlockDual : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G] (ν : G →* Kˣ) (m : ℕ),
    Nonempty (WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.dual (specialBlock ν m))
      (WeilDeligneRepresentation.twist (ν ^ (1 - (m : ℤ))) (specialBlock ν m)))

/-- The corrected dual-block identity
`(σ ⊗ S_m)^∨ ≅ (σ^∨ ⊗ ν^(1-m)) ⊗ S_m`. -/
def BlockDual : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G] (ν : G →* Kˣ)
    (σ : FiniteRepresentation.{uK, uG, uV} K G) (m : ℕ),
    Nonempty (WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.dual (block ν σ m))
      (block ν (FiniteRepresentation.twist (ν ^ (1 - (m : ℤ))) (FiniteRepresentation.dual σ)) m))

/-- Twisting a block twists its Weil factor and keeps its length. -/
def BlockTwist : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G] (ν χ : G →* Kˣ)
    (σ : FiniteRepresentation.{uK, uG, uV} K G) (m : ℕ),
    Nonempty (WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.twist χ (block ν σ m))
      (block ν (FiniteRepresentation.twist χ σ) m))

/-- Determinant, nilpotency order, length one and monodromy kernel of a block.
The kernel is the top-weight copy `ν^(m-1) ⊗ σ`. -/
def BlockInvariants : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G] (ν : G →* Kˣ)
    (σ : FiniteRepresentation.{uK, uG, uV} K G) (m : ℕ),
    FiniteRepresentation.determinantCharacter (block ν σ m).toFiniteRepresentation =
      FiniteRepresentation.determinantCharacter σ ^ m * ν ^ (σ.rank * (m * (m - 1) / 2)) ∧
    (block ν σ m).monodromy ^ m = 0 ∧
    (Nontrivial σ → ∀ n : ℕ, (block ν σ (n + 1)).monodromy ^ n ≠ 0) ∧
    Nonempty (WeilDeligneRepresentation.Equiv (block ν σ 1) (zeroMonodromy ν σ)) ∧
    ∀ n : ℕ, Nonempty (FiniteRepresentation.Equiv (kernelRepresentation (block ν σ (n + 1)))
      (FiniteRepresentation.twist (ν ^ n) σ))

/-- The monodromy kernel of a finite sum of blocks is the sum of the top-weight
copies of their Weil factors. -/
def BlockSumKernel : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G] (ν : G →* Kˣ) (k : ℕ)
    (d : Fin k → BlockDatum.{uK, uG, uV} K G),
    Nonempty (FiniteRepresentation.Equiv
      (kernelRepresentation (WeilDeligneRepresentation.directSum fun i => (d i).pair ν))
      (FiniteRepresentation.directSum fun i =>
        FiniteRepresentation.twist (ν ^ ((d i).length - 1)) (d i).representation))

/-- The monodromy kernel of a tensor product of blocks:
`⨁_{i < min m n} ν^(m+n-2-i) ⊗ σ ⊗ τ`. -/
def TensorBlockKernel : Prop :=
  ∀ (K : Type uK) [Field K] [CharZero K] (G : Type uG) [Group G] (ν : G →* Kˣ)
    (σ : FiniteRepresentation.{uK, uG, uV} K G) (τ : FiniteRepresentation.{uK, uG, uW} K G)
    (m n : ℕ),
    Nonempty (FiniteRepresentation.Equiv
      (kernelRepresentation (WeilDeligneRepresentation.tensor (block ν σ m) (block ν τ n)))
      (FiniteRepresentation.directSum fun i : Fin (min m n) =>
        FiniteRepresentation.twist (ν ^ (m + n - 2 - (i : ℕ))) (FiniteRepresentation.tensor σ τ)))

/-- Frobenius semisimplicity of blocks and of finite sums. A positive-length block
is Frobenius-semisimple exactly when its Weil factor is; its monodromy need not vanish. -/
def FrobeniusSemisimpleBlocks : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G] (ν : G →* Kˣ)
    (degree : G →* Multiplicative ℤ),
    (∀ (σ : FiniteRepresentation.{uK, uG, uV} K G) (n : ℕ),
      (block ν σ (n + 1)).IsFrobeniusSemisimple degree ↔
        (zeroMonodromy ν σ).IsFrobeniusSemisimple degree) ∧
    ∀ (k : ℕ) (A : Fin k → WeilDeligneRepresentation.{uK, uG, uV} K G ν),
      (WeilDeligneRepresentation.directSum A).IsFrobeniusSemisimple degree ↔
        ∀ i, (A i).IsFrobeniusSemisimple degree

/-- A rank-one pair has zero monodromy, is Frobenius-semisimple for every degree,
and is the zero-monodromy pair of its determinant character. -/
def RankOne : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G] (ν : G →* Kˣ)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν),
    A.rank = 1 →
      A.monodromy = 0 ∧
      (∀ degree : G →* Multiplicative ℤ, A.IsFrobeniusSemisimple degree) ∧
      Nonempty (WeilDeligneRepresentation.Equiv A
        (zeroMonodromy ν (FiniteRepresentation.determinant A.toFiniteRepresentation)))

/-- A pair whose Weil representation is semisimple is a finite sum of blocks
with irreducible Weil factors. No hypothesis on the group or on `ν` is needed. -/
def DecompositionExistence : Prop :=
  ∀ (G : Type uG) [Group G] (ν : G →* ℂˣ) (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν),
    A.toFiniteRepresentation.IsSemisimple →
      ∃ (k : ℕ) (d : Fin k → BlockDatum.{0, uG, uV} ℂ G),
        (∀ i, (d i).IsIrreducible) ∧
        Nonempty (WeilDeligneRepresentation.Equiv A
          (WeilDeligneRepresentation.directSum fun i => (d i).pair ν))

/-- Two finite sums of irreducible blocks are isomorphic exactly when there is a
bijection of summands preserving lengths and Weil factors up to isomorphism. -/
def DecompositionUniqueness : Prop :=
  ∀ (G : Type uG) [Group G] (ν : G →* ℂˣ) (k l : ℕ)
    (d : Fin k → BlockDatum.{0, uG, uV} ℂ G) (d' : Fin l → BlockDatum.{0, uG, uW} ℂ G),
    (∀ i, (d i).IsIrreducible) → (∀ j, (d' j).IsIrreducible) →
      (Nonempty (WeilDeligneRepresentation.Equiv
          (WeilDeligneRepresentation.directSum fun i => (d i).pair ν)
          (WeilDeligneRepresentation.directSum fun j => (d' j).pair ν)) ↔
        ∃ e : Fin k ≃ Fin l, ∀ i, (d i).length = (d' (e i)).length ∧
          Nonempty (FiniteRepresentation.Equiv (d i).representation (d' (e i)).representation))

/-- Indecomposability and irreducibility criteria for blocks, and the
indecomposable pairs with semisimple Weil representation. -/
def BlockCriteria : Prop :=
  ∀ (G : Type uG) [Group G] (ν : G →* ℂˣ),
    (∀ d : BlockDatum.{0, uG, uV} ℂ G, d.IsIrreducible →
      IsIndecomposable (d.pair ν) ∧
      (d.pair ν).toFiniteRepresentation.IsSemisimple ∧
      (LinearAlgebra.IsIrreducible (d.pair ν) ↔ d.length = 1) ∧
      ((d.pair ν).monodromy = 0 ↔ d.length = 1)) ∧
    (∀ (d : BlockDatum.{0, uG, uV} ℂ G) (d' : BlockDatum.{0, uG, uW} ℂ G),
      d.IsIrreducible → d'.IsIrreducible →
        (Nonempty (WeilDeligneRepresentation.Equiv (d.pair ν) (d'.pair ν)) ↔
          d.length = d'.length ∧
            Nonempty (FiniteRepresentation.Equiv d.representation d'.representation))) ∧
    (∀ A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν,
      A.toFiniteRepresentation.IsSemisimple →
        (IsIndecomposable A ↔
          ∃ d : BlockDatum.{0, uG, uV} ℂ G, d.IsIrreducible ∧
            Nonempty (WeilDeligneRepresentation.Equiv A (d.pair ν)))) ∧
    ∀ (k : ℕ) (d : Fin k → BlockDatum.{0, uG, uV} ℂ G), (∀ i, (d i).IsIrreducible) →
      ((WeilDeligneRepresentation.directSum fun i => (d i).pair ν).monodromy = 0 ↔
        ∀ i, (d i).length = 1)

/-- Decomposition of Frobenius-semisimple pairs with finite inertia image, and
the indecomposable ones, in the source setting: surjective degree with inertia
its kernel, and `ν(g) = q^(-degree g)`. -/
def FrobeniusSemisimpleClassification : Prop :=
  ∀ (G : Type uG) [Group G] (ν : G →* ℂˣ) (degree : G →* Multiplicative ℤ) (q : ℕ),
    Function.Surjective degree → Frobenius.NormCompatible (ν := ν) degree q →
    (∀ A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν,
      A.toFiniteRepresentation.HasFiniteInertiaImage degree.ker →
      A.IsFrobeniusSemisimple degree →
        ∃ (k : ℕ) (d : Fin k → BlockDatum.{0, uG, uV} ℂ G),
          (∀ i, (d i).IsIrreducible ∧
            (d i).representation.HasFiniteInertiaImage degree.ker) ∧
          Nonempty (WeilDeligneRepresentation.Equiv A
            (WeilDeligneRepresentation.directSum fun i => (d i).pair ν))) ∧
    (∀ d : BlockDatum.{0, uG, uV} ℂ G, d.IsIrreducible →
      d.representation.HasFiniteInertiaImage degree.ker →
        (d.pair ν).toFiniteRepresentation.HasFiniteInertiaImage degree.ker ∧
        (d.pair ν).IsFrobeniusSemisimple degree) ∧
    ∀ A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν,
      A.toFiniteRepresentation.HasFiniteInertiaImage degree.ker →
      A.IsFrobeniusSemisimple degree →
        (IsIndecomposable A ↔
          ∃ d : BlockDatum.{0, uG, uV} ℂ G, d.IsIrreducible ∧
            Nonempty (WeilDeligneRepresentation.Equiv A (d.pair ν)))

/-- Normal form of Frobenius-semisimple parameters, with compact inertia equal to
the kernel of the degree: every such parameter is a finite sum of blocks with
irreducible open-inertia-kernel Weil factors, every such sum is one, and every
rank has a Frobenius-semisimple parameter class. -/
def ParameterNormalForm : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ν : G →* ℂˣ) (degree : G →* Multiplicative ℤ) (q : ℕ),
    Function.Surjective degree → Frobenius.NormCompatible (ν := ν) degree q →
    CompactSpace degree.ker →
    (∀ A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν,
      IsFrobeniusSemisimpleParameter degree.ker degree A →
        ∃ (k : ℕ) (d : Fin k → BlockDatum.{0, uG, uV} ℂ G),
          (∀ i, (d i).IsIrreducible ∧
            (d i).representation.HasOpenInertiaKernel degree.ker) ∧
          Nonempty (WeilDeligneRepresentation.Equiv A
            (WeilDeligneRepresentation.directSum fun i => (d i).pair ν))) ∧
    (∀ (k : ℕ) (d : Fin k → BlockDatum.{0, uG, uV} ℂ G),
      (∀ i, (d i).IsIrreducible ∧ (d i).representation.HasOpenInertiaKernel degree.ker) →
        IsFrobeniusSemisimpleParameter degree.ker degree
          (WeilDeligneRepresentation.directSum fun i => (d i).pair ν)) ∧
    ∀ n : ℕ, Nonempty (FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν)
      degree.ker degree n)

/-- The complete block statement family. -/
def Statement : Prop :=
  SpecialBlockTensor.{uK, uG} ∧
  BlockTensor.{uK, uG, uV, uW} ∧
  SpecialBlockDual.{uK, uG} ∧
  BlockDual.{uK, uG, uV} ∧
  BlockTwist.{uK, uG, uV} ∧
  BlockInvariants.{uK, uG, uV} ∧
  BlockSumKernel.{uK, uG, uV} ∧
  TensorBlockKernel.{uK, uG, uV, uW} ∧
  FrobeniusSemisimpleBlocks.{uK, uG, uV} ∧
  RankOne.{uK, uG, uV} ∧
  DecompositionExistence.{uG, uV} ∧
  DecompositionUniqueness.{uG, uV, uW} ∧
  BlockCriteria.{uG, uV, uW} ∧
  FrobeniusSemisimpleClassification.{uG, uV} ∧
  ParameterNormalForm.{uG, uV}

end Langlands.WeilDeligneRepresentation.Blocks
