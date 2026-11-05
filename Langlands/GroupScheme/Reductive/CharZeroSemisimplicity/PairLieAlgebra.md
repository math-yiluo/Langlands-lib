# The tangent Lie algebra of a pair of representations

Author: Worker 1498. The complete-reducibility criterion
`Langlands.Algebra.complementedLattice_lieSubmodule_of_jordanClosed` that the last
theorem applies is by Worker 1429 (module `Langlands.Algebra.LinearLieSemisimplicity`).

This module is an internal helper for the proof of
`Langlands.GroupScheme.ReductiveCharZeroSemisimplicityStatement`, and it contains
the assembly of that proof. Let `σ : MatrixRepresentation G m` and
`ρ : MatrixRepresentation G n` be representations of a group scheme `G` over a
field `k`, with `G.X.hom` affine and locally of finite type. The two
representations act together, block diagonally, on `(m → k) × (n → k)`. Their
tangent endomorphisms form a Lie subalgebra `h` of `End ((m → k) × (n → k))`.
When `σ` is a closed embedding of a group with trivial unipotent radical, `h`
satisfies the hypotheses of the linear complete-reducibility criterion. Its
invariant subspaces control the rational subrepresentations of `ρ`. On `End V` the bracket is the ring
commutator, through the local instance `LieRing.ofAssociativeRing`.

## Declarations

- `prodMap_pow`: `(f.prodMap g) ^ r = (f ^ r).prodMap (g ^ r)`.
- `pairTangent σ ρ`: the `k`-linear map
  `Additive (lieKernel G k) → End ((m → k) × (n → k))` sending `X` to
  `toLin' (σ.tangentMatrix k X) ×ˢ toLin' (ρ.tangentMatrix k X)`, that is, to
  `prodMap` of the two tangent endomorphisms (`pairTangent_apply`, by `rfl`).
- `pairLieAlgebra σ ρ`: the range of `pairTangent σ ρ`, as a Lie subalgebra.
  `mem_pairLieAlgebra`: `x ∈ pairLieAlgebra σ ρ ↔ ∃ X, pairTangent σ ρ X = x`.
- `jordanSemisimplePart_mem_pairLieAlgebra` ([PerfectField k]): the Jordan
  semisimple part of every element of `pairLieAlgebra σ ρ` lies in it.
- `pairLieAlgebra_nilpotentIdeal_eq_bot` ([CharZero k], smooth, connected): if
  `G` has trivial unipotent radical and `σ` is a closed embedding, then every Lie
  ideal of `pairLieAlgebra σ ρ` consisting of nilpotent endomorphisms is `⊥`.
- `isSemisimpleRepresentation_of_pairLieAlgebra` (moreover `k` algebraically
  closed and `G.X.left` reduced): if the lattice of Lie submodules of
  `(m → k) × (n → k)` over `pairLieAlgebra σ ρ` is complemented, then
  `ρ.rationalRepresentation.IsSemisimpleRepresentation`. This is the Mathlib
  notion: the lattice of subrepresentations of the rational-point representation
  is complemented.
- `isSemisimpleRepresentation_of_isClosedSubgroup` (same hypotheses): if `G` has
  trivial unipotent radical and `σ` is a closed embedding, then
  `ρ.rationalRepresentation.IsSemisimpleRepresentation` for every `ρ`.

## Proofs

**Lie subalgebra.** For `X`, `Y`, the element `kernelBracket X Y` (module
`LieImage`) has tangent matrix `M N - N M` in every representation. So
`pairTangent (kernelBracket X Y)` is the commutator of `pairTangent X` and
`pairTangent Y`, block by block. One element works in both blocks because
`kernelBracket` does not depend on the representation.

**Jordan closure.** For `x = pairTangent X`, take `semisimpleKernel G X`. By
`jordanSemisimplePart_prodMap` (module `JordanClosure`), the semisimple part of a
`prodMap` is the `prodMap` of the semisimple parts. By
`toLin'_tangentMatrix_semisimpleKernel`, applied to `σ` and to `ρ`, each block is
the tangent endomorphism of `semisimpleKernel G X`.

**No nilpotent ideals.** Let `I` be an ideal of `h = pairLieAlgebra σ ρ` whose
elements are nilpotent. Let `π(f) = fst ∘ f ∘ inl` be the upper-left block, so
`π (pairTangent X) = toLin' (σ.tangentMatrix k X)`, and let `A = π(I)`, a
`k`-subspace of `End (m → k)`. Then:

- the elements of `A` are nilpotent, since by `prodMap_pow` the powers of a
  block-diagonal map are computed blockwise;
- they are tangent endomorphisms of `σ`;
- `A` is closed under the commutator with every tangent endomorphism of `σ`.
  The commutator of `toLin' (σ.tangentMatrix k Y)` with `π y` is `π` of the
  bracket `⁅pairTangent Y, y⁆ ∈ I`.

For `x ∈ I` with `x = pairTangent X`, we have `π x ∈ A`. So
`eq_one_of_nilpotent_normalized` (module `NilpotentIdeal`) gives `X = 1`, and hence
`x = pairTangent 0 = 0`.

**Transfer to rational subrepresentations.** Under the hypotheses of the section
(algebraically closed, characteristic zero, reduced, affine, locally of finite
type, smooth, connected), `isStableSubspace_iff_rationalMatrix` and
`isStableSubspace_iff_tangentMatrix` (module `TangentStability`) show that a
subspace of `n → k` is stable under all rational matrices of `ρ` iff it is stable
under all tangent matrices of `ρ`.

Let `W` be a subrepresentation of `ρ.rationalRepresentation`. Then `W` is
tangent-stable, so `(m → k) × W` is a Lie submodule `Wt` of `h`: the second
component of `pairTangent X (u, w)` is `ρ.tangentMatrix k X *ᵥ w`. Choose a Lie
complement `C` of `Wt`, and let `W'` be the image of `C` under the second
projection.

- `W'` is tangent-stable, since for `c ∈ C` the bracket `⁅pairTangent X, c⁆` lies
  in `C` and has second component `ρ.tangentMatrix k X *ᵥ c.2`. Hence `W'` is a
  rational subrepresentation.
- `W ∩ W' = 0`: if `c ∈ C` and `c.2 ∈ W`, then `c ∈ Wt ∩ C = 0`.
- `W + W' = n → k`: write `(0, v) = a + c` with `a ∈ Wt` and `c ∈ C`; then
  `v = a.2 + c.2`.

The lattice operations on subrepresentations are those on the underlying
submodules (`toSubmodule_inf`, `toSubmodule_sup`), so `W'` is a complement of `W`.

**Assembly.** `isSemisimpleRepresentation_of_isClosedSubgroup` applies
`complementedLattice_lieSubmodule_of_jordanClosed` to `pairLieAlgebra σ ρ`. The
no-nilpotent-ideal hypothesis is `pairLieAlgebra_nilpotentIdeal_eq_bot`, and the
Jordan-closure hypothesis is `jordanSemisimplePart_mem_pairLieAlgebra`.
Characteristic zero makes `k` perfect. The transfer theorem then concludes.

## Why the pair

The trivial-radical argument (Part A of `NilpotentIdeal`) works with the closed
embedding `σ`, because a nilpotent ideal has to be traced back to a unipotent
normal subgroup of `G` itself. The tangent image of `ρ` alone could have
nilpotent ideals coming from the kernel of `ρ`. The subspaces to be complemented,
however, live in the coordinate space of `ρ`. The pair Lie algebra, the image of
`lieKernel G k` under `σ ⊕ ρ`, carries both: its first block records `σ`, and its
second block acts on the coordinate space of `ρ`.
