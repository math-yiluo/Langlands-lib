# Character locality and faithfulness on arbitrary scheme tests

Fix a commutative ring `R` and abelian groups `M,N` in the scheme universe.
For every `T` over `Spec R`, an actual isomorphism between the base changes of
`D_R(M)` and `D_R(N)` is Zariski-locally induced by an additive equivalence
`N ≃+ M`, provided `N` is finitely generated as an additive monoid.

`exists_open_neighborhood_eq_restrictMap_on_test` gives, for each point of `T`,
an open immersion `a : W → T` containing that point and an equivalence `g`.
The equality is an equality of actual group-scheme morphisms:
`HomScheme.evaluate a e.hom` is the base change of `Diagonalizable.restrictMap R g`
to `W`. `relativeLocalCharacterModel` chooses the neighborhood and equivalence,
retaining the coverage and equality. In particular the assertion applies to
automorphisms of finite diagonalizable groups on arbitrary test schemes,
including nonreduced and disconnected schemes. The equivalence is chosen
locally; the theorem makes no globally constant choice on a disconnected test.

The proof restricts to an affine chart of `T` using `Descent.pullIso`. The canonical
diagonalizable base-change comparisons identify the pulled groups with diagonal
groups over that chart's ring. The affine locality theorem gives a further
principal open neighborhood. Naturality of the comparisons with character
restrictions and the pullback-composition comparisons then express its equality
in `HomScheme.evaluate` coordinates.

The module also proves faithfulness on every nonempty test:
`restrictMap_baseChange_injective` applies to all additive character maps, and
`restrictEquiv_baseChange_injective` to additive equivalences. These two results
do not require finite generation. Over a nonzero coefficient ring, faithfulness
follows from the linear independence of the degree monomials in the group
algebra. For a general nonempty test scheme, the proof pulls the equality to a
residue field at one point, uses naturality of the diagonalizable comparison,
and applies the nonzero-ring result.

All provenance is derived from the imported affine locality module, character
restriction formulas, actual base-change comparisons, and Mathlib residue
fields. There are no field or Noetherian hypotheses on the base. The
normalizer orbit-map comparison remains separate.
