# Block normal form of Frobenius-semisimple parameters

`Langlands.WeilDeligneRepresentation.Blocks.parameterNormalForm` proves the
published proposition
`Langlands.WeilDeligneRepresentation.Blocks.ParameterNormalForm.{uG, uV}`
from `Langlands/WeilDeligne/BlockStatements.lean`, for arbitrary universes
`uG uV`:

```lean
theorem parameterNormalForm : ParameterNormalForm.{uG, uV}
```

The setting is a topological group `G`, a character `ν : G →* ℂˣ`, a degree
`degree : G →* Multiplicative ℤ` and a natural number `q`. The degree is
surjective, `Frobenius.NormCompatible degree q` holds (`1 < q` and
`ν g = q ^ (-degree g)`), and the inertia subgroup `degree.ker` is compact. The
statement has three clauses:

1. Every Frobenius-semisimple parameter `A` is isomorphic to a finite direct sum
   `directSum fun i => (d i).pair ν` of blocks. Each Weil factor is irreducible
   and has open inertia kernel.
2. Conversely, every such direct sum is a Frobenius-semisimple parameter.
3. For every `n`, there is a Frobenius-semisimple parameter class of rank `n`.

The theorem is
`ParameterNormalForm.parameterNormalForm_of_decompositionExistence` applied to
the Library proof `Blocks.decompositionExistence` of
`Blocks.DecompositionExistence`, from
`Langlands/WeilDeligne/DecompositionExistenceProof.lean`. The reduction
theorem `parameterNormalForm_of_decompositionExistence` assumes
`DecompositionExistence.{uG, uV}` and proves the three clauses with
`exists_blocks`, `isFrobeniusSemisimpleParameter_directSum` and
`nonempty_classesOfRank`. Apart from the final theorem, every declaration is in
the namespace `Langlands.WeilDeligneRepresentation.ParameterNormalForm`. The
helper lemmas are in `Langlands/WeilDeligne/ParameterNormalFormHelpers.lean`,
documented in `ParameterNormalFormHelpers.md`.

Sources: Tate 1979 (`tate-1979-number-theoretic-background`), 4.1.3–4.1.5,
and Henniart 2002 (`henniart-2002-characterization`), §2.2–2.3. The statement's
Markdown `Langlands/WeilDeligne/BlockStatements.md` sketches a route through
Maschke's theorem on eigenspaces and Schur's lemma. The implemented proof
instead follows Tate's own argument in 4.1.3. For `g` of nonzero degree, the
subgroup `zpowers g ⊔ ker ρ` has finite index because the inertia image is
finite, and `ρ g` generates its image. The Library's finite-index restriction
theorem then transfers semisimplicity in both directions.

## Kernels of blocks and sums

- `representation_eq_one_of_block`: if `x` acts trivially on
  `block ν σ m` with `0 < m`, then `x` acts trivially on `σ`. The block action
  is `σ(x) ⊗ Special.action ν m x`, and the special action fixes the basis
  vector `e_0` (it multiplies coordinate `j` by `ν(x) ^ j`). So
  `σ(x) v ⊗ e_0 = v ⊗ e_0` for all `v`. Applying `id ⊗ proj_0` followed by
  `TensorProduct.rid` gives `σ(x) v = v`.
- `representation_eq_one_of_directSum`: if `x` acts trivially on a direct sum
  `FiniteRepresentation.directSum A`, then `x` acts trivially on every summand.
  The action is `DirectSum.lmap`, so this follows from `DirectSum.lmap_lof` and
  injectivity of `DirectSum.of`.

## Inertia

- `hasFiniteInertiaImage_of_hasOpenInertiaKernel`: if the inertia subgroup is
  compact, an open inertia kernel gives a finite inertia image. This is the
  Library lemma `Langlands.Weil.finite_range_of_open_kernel` applied to the
  restriction of the representation to inertia.
- `hasOpenInertiaKernel_of_forall`: a representation on which inertia acts
  trivially has open inertia kernel, since its inertia kernel is the whole
  inertia subgroup.

## Clause 1: `exists_blocks`

Let `A` be a Frobenius-semisimple parameter. By surjectivity, choose `Φ` with
`degree Φ = ofAdd 1`. The inertia kernel of `A` is open, so the inertia image is
finite. Frobenius semisimplicity at `Φ`, which has nonzero degree, makes
`A.representation Φ` semisimple. The helper
`isSemisimpleRepresentation_of_isSemisimple` (one direction of Tate's
criterion) shows that the Weil representation of `A` is semisimple.
`DecompositionExistence` then gives block data `d` with irreducible Weil factors
and an isomorphism `e` from `A` to the direct sum of the blocks.

It remains to show that each Weil factor `(d i).representation` has open
inertia kernel. The inverse isomorphism `e.symm` is an injective intertwining
map into `A`. By the Library lemma
`FiniteRepresentation.hasOpenInertiaKernel_of_injective`, the direct sum has
open inertia kernel. An inertia element in the kernel of the direct sum acts
trivially on the `i`-th block (`representation_eq_one_of_directSum`), hence on
its Weil factor (`representation_eq_one_of_block`, because block length is
positive). Therefore the inertia kernel of the factor contains the open inertia
kernel of the sum, and `Subgroup.isOpen_mono` shows that it is open.

## Clause 2: `isFrobeniusSemisimpleParameter_directSum`

Let `d` be block data with irreducible Weil factors with open inertia kernels.

*Open inertia kernel.* By the Library lemmas
`FiniteRepresentation.hasOpenInertiaKernel_directSum` and
`FiniteRepresentation.hasOpenInertiaKernel_tensor`, it suffices that each Weil
factor and each special block have open inertia kernel. The first is a
hypothesis. For the special block: on inertia, `ν x = q ^ 0 = 1` by
`NormCompatible`. So the special action, which multiplies coordinate `j` by
`ν(x) ^ j`, is the identity, and `hasOpenInertiaKernel_of_forall` applies.

*Frobenius semisimplicity.* Let `g` have nonzero degree. The action of `g` on
the direct sum is `DirectSum.lmap` of the block actions, and the action on the
`i`-th block is `σ_i(g) ⊗ diag(1, ν(g), …, ν(g)^(m_i - 1))`. By the helpers
`isSemisimple_lmap` and `isSemisimple_map_diag`, it suffices that each
`σ_i(g)` is semisimple. The factor `σ_i` is irreducible: its lattice of
subrepresentations is a simple order, hence complemented, so `σ_i` is a
semisimple representation. Its inertia image is finite
(`hasFiniteInertiaImage_of_hasOpenInertiaKernel`). Choose `Φ` of degree one.
The helper `isSemisimple_of_isSemisimpleRepresentation` (the other direction
of Tate's criterion) shows that `σ_i(g)` is semisimple.

## Clause 3: `nonempty_classesOfRank`

Let `T` be the trivial representation of `G` on `ULift (Fin n → ℂ)`, which lies
in the carrier universe `uV`. The pair `zeroMonodromy ν T` is a
Frobenius-semisimple parameter. Inertia acts trivially, so the inertia kernel
is open (`hasOpenInertiaKernel_of_forall`). Every element acts by the
identity, which is semisimple. Its class has rank
`finrank ℂ (ULift (Fin n → ℂ)) = n` (`finrank_ulift`, `Module.finrank_fin_fun`).
