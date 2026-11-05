# Homomorphism descent to split tori from pointed domination

Worker 1485 assembles descended coordinate characters into an actual
homomorphism to a split torus and applies Worker 1376's character descent.
This internal construction uses the finite-product universal property,
existing actual base-change comparisons and faithful field pullback.
It cites no external assertion.

Let `k` be a field, let `G` be a reduced affine actual group scheme
over `k` with `HasPointedSplitTorusDomination G`, and let `T` be a
supplied split torus over `k`. For any field extension `K/k`, with both
carriers in any common universe `u`,
`HasPointedSplitTorusDomination.splitTorusHomEquiv` is an equivalence
from the actual group-scheme homomorphisms `G → T` to those
`G_K → T_K`. Its forward map is exactly actual group-scheme base
change along `algebraBaseMap k K`. Its inverse descends the supplied
extension-field map; `baseChange_splitTorusHomEquiv_symm` proves recovery,
and `existsUnique_splitTorusHom` states the resulting unique descent.
There is no remaining character-surjectivity premise in these results.
The equalities concern represented morphisms, so hold on all scheme tests.

The supporting general construction works for any base morphism
`b : S' → S`, an actual group scheme `H` over `S`
and an actual split torus `D` over `S`. Suppose every character
`H_{S'} → Gm_{S'}` is the base change of a character of `H`, followed by
the canonical multiplicative-group comparison. Then every actual
homomorphism `H_{S'} → D_{S'}` is the base change of a homomorphism
`H → D`. Over a field extension `K/k` in any common universe `u`,
the latter descent is unique. The source need not be commutative.

The proof first records the coordinate projection identity for the
existing split-torus base-change isomorphism. It obtains each coordinate
of the requested descended map by the assumed surjectivity on
characters, and forms the map by `Pi.lift`. Equality after base change
follows by checking all coordinate projections. An actual splitting
isomorphism for `D` reduces the general split-torus target to this
coordinate case. For fields, faithful pullback proves uniqueness of the
underlying morphism and hence of the actual group homomorphism.

The general construction keeps its character-surjectivity premise explicit
and uses no reducedness, smoothness, affineness, connectedness or finite-type
hypothesis on the source. The final application discharges this premise
by `HasPointedSplitTorusDomination.exists_character` from
`SplitTorusCharacterDescent`, using precisely the reducedness, affineness
and pointed domination stated above. Faithful pullback supplies injectivity;
the resulting bijection is packaged with `Equiv.ofBijective`.

The final application adds no smoothness, connectedness, solvability,
finite-type, separability, algebraicity, characteristic, perfection or
infinitude restriction. It does not supply a torus quotient, dominance,
an fppf property, kernel geometry, unipotence, split unipotence or the final
split geometric radical theorem. Those remain separate obligations.
