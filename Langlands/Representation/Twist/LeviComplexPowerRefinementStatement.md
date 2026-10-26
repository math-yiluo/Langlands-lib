# Complex determinant characters through actual Levi refinements

Author: Worker 429.

`Langlands.LeviComplexPowerRefinementStatement.{uF,uV}` states three related
compatibilities for the published complex determinant characters and scalar
twists. It is a closed proposition definition; this module supplies no proof.
The field and representation-carrier universes are independent.

Fix any prime `p`, actual `PadicField F`, compatible realization `T`, natural
rank `n`, coarse block shape `B`, refinement `S`, and complex exponent
`z : Fin B.length → ℂ`. Put `C = B.flatten S` and
`e = Geometric.flattenedLeviEquiv F.Carrier B S`. For each fine block `k`, the
repeated exponent is

```text
zFine k = z (((B.flattenBlockEquiv S).symm k).1).
```

The inverse ordered block equivalence identifies the actual coarse block
containing `k`. The exponent is a determinant exponent: no block-size
multiplier or division is inserted. The character remains exactly
`T.leviComplexPowerCharacter`, using the existing residue-normalized absolute
value and complex powers.

The first law quantifies over every element `q` of the actual
`Geometric.refinedParabolic F.Carrier B S`. It equates the coarse character of
`q.val` with the fine character at `zFine` of
`e.symm (Geometric.refinedLeviProjection F.Carrier B S q)`. Both sides are
actual complex units. Thus the proposed law includes restriction through the
unipotent directions of this parabolic.

The second law is equality of actual monoid homomorphisms from
`Geometric.refinedLevi F.Carrier B S` to `ℂˣ`. On the left the coarse character
is precomposed with the actual subgroup inclusion. On the right the fine
character at `zFine` is precomposed with `e.symm.toMonoidHom`.

The third law retains every complex module `V : Type uV`, every representation
`ρ` of the actual fine product Levi on `V`, and every existing fine exponent
`a : Fin C.length → ℂ`. Pull back the fine twist at `a` along `e.symm`, then
twist it by the restricted coarse character. The result is equal, as a
representation on the same carrier, to the pullback of the fine twist at
`a + zFine`. This is equality of the full actions, not merely equality of
parameter functions or an assertion that an unspecified equivalence exists.

All ranks, including zero, all central determinant directions, arbitrary
complex exponents and the actual ordered nested blocks are retained. No
positivity, smoothness, admissibility, irreducibility, unitarity, temperedness,
chamber, support, zero-sum or tensor-factorization hypothesis is imposed.

The provenance is internal. In the intended separate proof, each coarse
parabolic block is block triangular, so its determinant is the product of the
fine diagonal-block determinants. Applying the normalized absolute-value
character and its complex power, then reindexing by `flattenBlockEquiv`, should
give the first law. The actual refined-Levi section should give the second,
and the published additive complex character identity should give the third.
This paragraph describes a proof route, not a proof provided here, and claims
no external source theorem.

The published real analogue `Langlands.refinedLeviRealTwist` also treats
normalized induction and specified quotient maps; those conclusions are
separate. This statement proves no compatibility, induced-family construction,
shape-equality adapter, selected-branch continuation, Jacquet occurrence,
multiplicity comparison, quotient extraction, cone bound, irreducible head or
supported all-regular comparison.
