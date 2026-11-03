# Combinations of commuting cocharacters and extension from a Levi

Author: Worker 1280.

This internal construction supports the simultaneous dynamic realization target.
It does not prove existence of a coefficient satisfying the required inclusions.
All results here hold over an arbitrary base scheme, on every original test
scheme, including nonreduced tests.

`commutingProduct χ tau htau` is the group-scheme cocharacter whose value is
`χ(t) tau(t)`. The hypothesis says that the image of `tau` lies in the actual dynamic
centralizer of `χ`. Its all-refinement centralizer condition proves that the
pointwise formula is multiplicative, and its naturality gives an actual
homomorphism through the fully faithful group-valued Yoneda functor.

`cocharacterCombination χ tau htau n` has value `χ(t^n) tau(t)` for an arbitrary
integer `n`. Its conjugation orbit on any point of `Z(χ)` is exactly the
conjugation orbit of `tau`: the first factor commutes with the point and with
`tau`. A cocharacter `ν` of a representative `j : L → G` of `Z(χ)` automatically
has centralizing ambient image `tau = ν ≫ j`.

`realization_of_inclusions` proves the desired exact products for a supplied
ambient cocharacter `ψ`, conditional on the three inclusions

- `P(ψ) ≤ P(χ)`;
- `U(χ) ≤ U(ψ)`;
- `Z(ψ) ≤ Z(χ)`;

and equality of the `ψ` and `ν ≫ j` orbit morphisms on points in the image of
`j`. The closedness of `j` reflects the parabolic, centralizer and unipotent
conditions, yielding equality of their preimages. For separated `G`, a point
`g` of `P(χ)` has a centralizer limit `z`; the point `z⁻¹ g` lies in `U(χ)`.
Lift `z` through `j`. For either `E = P(ψ)` or `E = U(ψ)`, the assumptions put
both `g` and this unipotent factor in `E`, so the lifted centralizer factor
lies in `E.comap j`. This proves the literal same-test product. Centralizer
image equality follows from the centralizer inclusion and its preimage equality.

`realization_cocharacterCombination_of_inclusions` applies this reduction to
`cocharacterCombination χ (ν ≫ j) _ n`. The restricted-orbit hypothesis is
then automatic, leaving exactly the three inclusions as premises.

These are derived algebraic consequences of the Library's existing all-test
centralizer, closed-subgroup reflection and separated dynamic limit
constructions. They claim no new literature theorem. To prove the full target
one must still produce a combination with the three inclusions, uniformly in
all test schemes. No reductivity or finite-type assertion is established here.
