# Reductive quotients of represented dynamic parabolics

This is an internal consequence of published dynamic representability,
smoothness, connectedness, centralizer reductivity and the scheme level Levi
decomposition. It introduces no independent assertion from the literature.
Its purpose is to provide the local quotient construction in the proof of the
relative parabolic reductive quotient theorem.

`DynamicReductiveQuotientStatement` says that, for every universe and every
scheme `S`, if `G` is reductive, `iP : P → G` represents the dynamic parabolic
of a cocharacter `χ`, and `r : U → P` composed with `iP` represents the
contracting subgroup of `χ`, then there are a reductive group scheme `Z` and
an fppf quotient `P → Z` with kernel the all-test-scheme range of `r`.
The statement does not assert that arbitrary relative parabolics have such a
global cocharacter presentation, nor does it glue local quotients.

The implemented proof first proves `Dynamic.isReductive_centralizer`.
The published arbitrary-base dynamic smoothness theorem makes a closed
centralizer representative smooth. Closedness in the affine ambient group
makes it affine over `S`. For each geometric point of `S`, base change of the
representing homomorphism represents the centralizer of the base changed
cocharacter. The ambient geometric fibre is pseudo-reductive over an
algebraically closed field, hence connected reductive. The published field
centralizer theorem makes its centralizer connected reductive and therefore
pseudo-reductive, exactly as required by `IsReductive`.

Next `Dynamic.isFppfQuotient_limitGroupHom_range` identifies the supplied
contracting representative with the kernel of the dynamic limit map.
The isomorphism of representatives is compatible with their maps into `G`;
monicity of the represented parabolic cancels the map into `G`.
Precomposing by that isomorphism preserves the range subgroup functor.
The published smooth limit-map quotient theorem then gives the fppf quotient
with the specified range of `r`, rather than only with its canonical kernel.

Finally `dynamicReductiveQuotient` chooses a closed centralizer representative
by arbitrary-base dynamic representability. Arbitrary-base dynamic
smoothness supplies smoothness of `U`, and the preceding two lemmas give the
reductive target and quotient map.
