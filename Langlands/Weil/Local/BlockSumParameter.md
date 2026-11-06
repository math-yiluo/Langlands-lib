# Sums of special blocks on irreducible local Weil representations are parameters

Author: Worker 1704.

## Scope and provenance

This is internal support infrastructure for the surjectivity half of
`Langlands.Correspondence.AssemblyBijectiveStatement`. To show that a
representation class is assembled from some parameter class, one has to build
the Frobenius-semisimple parameter `⊕_i σ_i ⊗ Sp(m_i)` from irreducible Weil
classes `σ_i`. This module proves that the published block sum is such a
parameter and packages its class.

It formalizes no literature theorem. The arguments are standard linear algebra
(an endomorphism killed by a squarefree polynomial is semisimple, and so on),
combined with the proved local Weil-group facts in
[RepresentationProof.md](RepresentationProof.md) and the published definitions
of blocks, direct sums and parameters in
[../../WeilDeligne/SpecialBlocks.md](../../WeilDeligne/SpecialBlocks.md),
[../../WeilDeligne/DirectSum.md](../../WeilDeligne/DirectSum.md) and
[Parameters.md](Parameters.md). No hypothesis is assumed beyond what each
theorem's type states.

## Linear algebra (namespace `Langlands.BlockSumParameter`)

All of these are about `Module.End.IsSemisimple` over a field `K`.

- `isSemisimple_of_pow_eq_one`: in characteristic zero, if `f ^ n = 1` with
  `n ≠ 0` then `f` is semisimple. `f` is killed by `X ^ n - 1`, which is
  separable, hence squarefree.
- `isSemisimple_rTensor`, `isSemisimple_lTensor`: for `M` (resp. `N`) finite
  dimensional, `f ⊗ 1` (resp. `1 ⊗ g`) is semisimple when `f` (resp. `g`) is.
  The squarefree minimal polynomial of `f` also kills `f ⊗ 1`, because
  `rTensorAlgHom` (resp. `lTensorAlgHom`) is an algebra map.
- `isSemisimple_tensorMap`: over a perfect field, with `M` and `N` finite
  dimensional, `TensorProduct.map f g` is semisimple when `f` and `g` are. It is
  the product of the commuting semisimple maps `f ⊗ 1` and `1 ⊗ g`
  (Mathlib's `IsSemisimple.mul_of_commute`).
- `aeval_lmap_apply`: evaluating a polynomial at the componentwise map
  `DirectSum.lmap f` acts on each component as evaluation at `f i`.
- `isSemisimple_lmap`: over a finite index type with finite-dimensional
  components, `DirectSum.lmap f` is semisimple when every `f i` is. The radical
  of `∏ i, minpoly (f i)` is squarefree and is divisible by each squarefree
  `minpoly (f i)`, so it kills every component.
- `isSemisimple_specialAction`: the weight action
  `WeilDeligneRepresentation.Special.action ν m g`, which multiplies the
  coordinate `j` by `ν(g) ^ j`, is semisimple for any group `G` and character
  `ν : G →* Kˣ`. It is multiplication by an element `c` of `K^m`, and it is
  killed by `∏ (X - a)`, the product taken over the distinct values `a` of `c`.

## Finite image (namespace `Langlands.FiniteRepresentation`)

- `exists_pow_eq_one_of_hasFiniteImage`: if a complex finite representation
  `A` of a group has finite image, then every `A.representation g` has a
  positive power equal to `1`. The powers of `g` cannot all have distinct
  images, so the unit `A.representation g` has finite order.
- `isSemisimple_of_hasFiniteImage`: then every `A.representation g` is
  semisimple, by `isSemisimple_of_pow_eq_one`.

## Local Weil group (namespace `Langlands.Weil.Local`)

Fix a prime `p`, `[Fact p.Prime]` and `F : PadicField.{u} p`; representations
have carriers in an arbitrary universe `v`. The norm character is
`localNormCharacter F`.

- `isSemisimple_of_isContinuous_isIrreducible`: if a local Weil representation
  `A` is continuous and irreducible, then `A.representation g` is semisimple
  for every `g`. The proved reduction `localWeilIrreducibleReductionFor`
  makes `A` equivalent to an unramified twist `χ_z ⊗ B` of a representation
  `B` with finite image. `B.representation g` is semisimple, so is the scalar
  multiple `χ_z(g) • B.representation g`, and semisimplicity is transported
  along the equivalence (`LinearEquiv.isSemisimple_iff`).
- `specialAction_inertia`: on an inertia element the weight action of the norm
  character is the identity, since inertia is the kernel of the norm character
  (`localNormFaithfulnessFor`).
- `block_hasOpenInertiaKernel`: for continuous `A` and any `m`, the block
  `WeilDeligneRepresentation.block (localNormCharacter F).toMonoidHom A m` has
  open inertia kernel. The Weil part of `A` has open inertia kernel by
  `localWeilContinuity`. The special factor's inertia kernel is all of inertia
  by `specialAction_inertia`. The published
  `FiniteRepresentation.hasOpenInertiaKernel_tensor` combines the two.
- `isLocalFrobeniusSemisimpleParameter_block`: for continuous irreducible `A`
  and any `m`, that block is a Frobenius-semisimple parameter
  (`IsLocalFrobeniusSemisimpleParameter`). At every Weil element its action is
  the tensor product of the semisimple action of `A` and the semisimple weight
  action, and `ℂ` is perfect. The parameter definition only asks for
  semisimplicity at elements of nonzero degree, and here it holds at all of
  them.
- `isLocalFrobeniusSemisimpleParameter_directSum`: a finite direct sum (any
  universe `uι` of finite index types with decidable equality) of
  Frobenius-semisimple parameters is one. The published
  `hasOpenInertiaKernel_directSum` gives the open inertia kernel, and
  `isSemisimple_lmap` gives semisimplicity.
- `isLocalFrobeniusSemisimpleParameter_blockSum`: for `B : ι → LocalWeilRepresentation F`
  with every `B i` continuous and irreducible, and any lengths `m : ι → ℕ`,
  the direct sum `⊕_i block ν (B i) (m i)` is a Frobenius-semisimple parameter.

## The parameter class

- `blockSumParameterClass F B hB m` (a `def`): for
  `B : Fin r → LocalWeilRepresentation.{u, v} F`, a proof `hB` that every
  `B i` is continuous and irreducible, and `m : Fin r → ℕ`, this is the element
  of `LocalFrobeniusSemisimpleParameterClassesOfRank.{u, v} F (∑ i, (B i).rank * m i)`
  given by the class of the block sum `⊕_i block ν (B i) (m i)` with the
  parameter proof above. The rank proof uses the published
  `rank_directSum` and `rank_block`.
- `forget_blockSumParameterClass`: the forgetful map
  `WeilDeligneRepresentation.ParameterRelations.forget` sends this class to
  `WeilDeligneRepresentation.classOf` of the same block sum. This holds by
  definition (`rfl`).

The assembly relation `Correspondence.IsBlockSum` uses blocks of length
`m i + 1`. A user instantiates `m` here with `fun i => m i + 1`.
