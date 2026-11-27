# Central radicals under restriction and extension of scalars

The module `Langlands.Algebra.LieCentralRadicalBaseChange` proves that reductivity of a
finite-dimensional Lie algebra in characteristic zero survives restriction of scalars to a
subfield followed by extension of scalars to an arbitrary extension of that subfield. In this
file a Lie algebra is called reductive when it satisfies Mathlib's
`LieAlgebra.HasCentralRadical` (its radical equals its centre).

## Main results

- `map_derivedSeriesOfIdeal`: a surjective Lie algebra homomorphism carries the derived series of
  an ideal onto the derived series of the image ideal.
- `radical_le_center_of_surjective`: if a surjective homomorphism `L → L'` onto a Lie algebra with
  trivial radical has central kernel, then the radical of `L` is central.
- `hasCentralRadical_of_lieEquiv`: having central radical is invariant under isomorphisms of
  Noetherian Lie algebras.
- `quotientHom`, `hasTrivialRadical_quotient_center`: the quotient of a reductive Lie algebra by
  its centre has trivial radical.
- `hasTrivialRadical_restrictScalars`: trivial radical passes from a Lie algebra over `F` to the
  same Lie algebra viewed over a subfield `k` (`RestrictScalars k F S`).
- `toMatrix_baseChange`, `isKilling_baseChange`, `hasTrivialRadical_baseChange`: in characteristic
  zero a finite-dimensional Lie algebra with trivial radical has non-degenerate Killing form
  (Cartan's criterion, Mathlib's `HasTrivialRadical.instIsKilling`); the Gram matrix of the
  base-changed Killing form is the image of the original Gram matrix, so its determinant stays
  non-zero, and the scalar extension again has trivial radical.
- `baseChangeHom`: the scalar extension of a Lie algebra homomorphism.
- `hasCentralRadical_baseChange_restrictScalars`: **if `L` is a finite-dimensional Lie algebra
  over a finite extension `F` of a field `k` of characteristic zero with central radical, then
  `K ⊗[k] RestrictScalars k F L` has central radical for every field extension `K` of `k`.**

## Proof of the main result

Write `S = L / z(L)`. It has trivial radical, hence so does `RestrictScalars k F S`, hence so does
`K ⊗[k] RestrictScalars k F S` (Killing form argument above). The quotient map, restricted to `k`
and extended to `K`, is a surjection `π : K ⊗ L → K ⊗ S`. Over a field the tensor product is
exact, so the kernel of `π` is the image of `K ⊗ z(L)`, which is central in `K ⊗ L`. Then
`radical_le_center_of_surjective` shows that the radical of `K ⊗ L` is central; the reverse
inclusion holds in every Lie algebra.

## Sources

Cartan's criterion and the description of reductive Lie algebras as those whose radical is the
centre are standard (N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §5 and §6.4); the
Lean proofs here use Mathlib's versions of these facts.
