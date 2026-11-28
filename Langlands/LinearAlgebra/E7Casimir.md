# The Casimir identity for root data of type E₇

Module: `Langlands.LinearAlgebra.E7Casimir`.

## Main result

`E7Casimir.sum_toLinearMap_coroot_smul_root` concerns a root datum `P : RootDatum ι M N`
over `ℤ` with finitely many roots (`[Fintype ι]`), assumed reduced (`[P.IsReduced]`), together
with a base `b : P.Base` and a numbering `s : Fin 7 → ι` of its simple roots. The hypotheses are:

- `hA`: the pairings of the numbered simple roots are the entries of Mathlib's Cartan matrix,
  `P.pairing (s i) (s j) = CartanMatrix.E 7 i j`;
- `hs`, `hsupp`: `s` takes values in `b.support` and every element of `b.support` is some
  `s k`;
- `hspan`: the coroots span the cocharacter lattice, `P.corootSpan ℤ = ⊤`.

The conclusion is that every character `x : M` satisfies

`∑ᵢ ⟨x, αᵢ^∨⟩ αᵢ = 36 x`,

the sum running over all roots `αᵢ`, with `⟨x, αᵢ^∨⟩ = P.toLinearMap x (P.coroot i)`.

The constant `36` is twice the Coxeter number `18` of `E₇`. The identity says that the map
`x ↦ ∑ᵢ ⟨x, αᵢ^∨⟩ αᵢ` on the character lattice is multiplication by `36`.

## The root tables

`rootCoeff : Fin 126 → Fin 7 → ℤ` lists the coefficient vectors, in the simple roots numbered
as in `CartanMatrix.E 7`, of the `126` roots of `E₇`. The list increases strictly in the key
`rootKey c = ∑ₖ cₖ 9ᵏ` (`rootKey_lt`), so the list has no repetitions (`rootCoeff_injective`).
Auxiliary tables record, for each listed vector, the position of its image under each simple
reflection (`reflIndex`), the position of its negative (`negIndex`), the positions of the simple
roots (`simpleIndex`), and a parent of smaller depth (`parent`, `parentVertex`, `depth`) from
which it is obtained by one simple reflection. Here the simple reflection in vertex `m` acts on
coefficient vectors by `RootReflectionCoefficients.reflect (CartanMatrix.E 7) m`. All the
properties of these tables that the proofs use, including the matrix identity

`∑ₐ cₐ cₐᵀ · E₇ = 36 · I` (`sum_rootCoeff_mul`),

where `cₐ` runs over the `126` listed vectors and `E₇` is the Cartan matrix, are checked by
`decide +kernel`.

## Proof

Write `comb c = ∑ₖ cₖ α_{s k}` and `cocomb c = ∑ₖ cₖ α_{s k}^∨`. Under `hA`, reflection of an
actual root in a numbered simple root acts on a coefficient vector `c` with
`α = comb c`, `α^∨ = cocomb c` by `reflect` (`reflectionPerm_spec`).

1. Every listed vector is the coefficient vector of an actual root and of its coroot
   (`exists_index`): induction on `depth`, using the parent table.
2. Every actual root is listed (`exists_rootCoeff`): Mathlib's induction principle
   `RootPairing.Base.induction_reflect` reduces this to simple roots, negatives (the table
   `negIndex`) and simple reflections (the table `reflIndex`).
3. The numbered simple roots are linearly independent over `ℤ` (they are distinct by
   `injective_of_cartan`, since off-diagonal entries of `CartanMatrix.E 7` are nonpositive), so
   the choice of a root for each listed vector is injective. Together with step 2 it is a
   bijection, and the sum over all roots becomes the sum over the `126` listed vectors.
4. Since the perfect pairing is injective on characters, it suffices to compare both sides
   after pairing with each simple coroot, because the simple coroots span the cocharacter
   lattice (`RootPairing.Base.span_int_coroot_support` and `hspan`). After exchanging the
   sums, this comparison is the identity `sum_rootCoeff_mul`.

## Transport along equivalences

For an equivalence `f : RootPairing.Equiv P Q` of root data, its weight map `W` and index
bijection `σ` satisfy `⟨W x, α^∨_{σ i}⟩ = ⟨x, α^∨_i⟩`
(`toLinearMap_weightMap_coroot_indexEquiv`). Hence `W` carries the sum `∑ᵢ ⟨x, αᵢ^∨⟩ αᵢ` of
`P` to the corresponding sum of `Q` (`weightMap_sum_toLinearMap_coroot_smul_root`). For any
integer `c`, the identity `∑ᵢ ⟨x, αᵢ^∨⟩ αᵢ = c x` for all `x` therefore holds for `Q` when it
holds for `P` (`sum_toLinearMap_coroot_smul_root_of_equiv`) and for `P` when it holds for `Q`
(`sum_toLinearMap_coroot_smul_root_of_equiv_symm`).

## Provenance

These are internal results about Mathlib's root data and Mathlib's matrix `CartanMatrix.E 7`.
The list of roots is finite data whose required properties are checked in Lean; no
classification theorem is assumed. The reflection formula on coefficient vectors comes from the
module `Langlands.LinearAlgebra.RootReflectionCoefficients`.
