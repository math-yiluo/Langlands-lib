# Exact nesting from simultaneous Levi realization

Author: Worker 1212.

This internal algebraic adapter derives the full all-test nested decomposition
from the simultaneous realization identities. It connects a source cocharacter
in a represented dynamic Levi to the literal subgroup products needed for
induction in stages.

Let `G` and `L` be group schemes over any scheme `S`, let `χ` be a cocharacter
of `G`, and let `j : L → G` represent `Z(χ)`. For a cocharacter `ν` of `L`
and an ambient cocharacter `ψ`, the three comparison hypotheses are

- `P(ψ) = extendFromCentralizer χ j hj P(ν)`;
- `Z(ψ) = Z(ν).map j`;
- `U(ψ) = extendFromCentralizer χ j hj U(ν)`.

`realized_parabolic_le` uses the first identity and the published inclusion of
every exact extension in `P(χ)`. `realized_centralizer_le` uses the second
identity, the inclusion of an actual image in `range j`, and the representing
equality `range j = Z(χ)`. `unipotent_le_realized` uses the third identity and
the published inclusion of `U(χ)` in every exact extension. Thus these identities
give `P(ψ) ≤ P(χ)`, `Z(ψ) ≤ Z(χ)` and `U(χ) ≤ U(ψ)`. These three conclusions
need neither separatedness nor closedness of `j`.

With separatedness of `G`, `nestedLeviDecomposition_of_realization` applies the
published `nestedLeviDecomposition_of_inclusions` to those proved inclusions.
For every original test scheme `X`, put `H = Z(χ)(X) ∩ P(ψ)(X)`,
`V = Z(χ)(X) ∩ U(ψ)(X)` and `W = Z(ψ)(X)`. The conclusion states that
`V` and `W` lie in `H`, that the copy of `V` in `H` is normal and complementary
to the copy of `W`, and gives all three actual set products

- `H = W V`;
- `U(ψ)(X) = V U(χ)(X)`;
- `P(ψ)(X) = H U(χ)(X)`.

The factors and products are evaluated on the same `X`; no extension of the
test scheme or replacement of the actual images occurs. The first factor is
the Levi factor in the displayed products, as in the imported predicate.

`exists_realization_with_nestedDecomposition` discharges the realization
hypotheses for every connected reductive `G` over any field, every `χ`, every
closed representative `j` of `Z(χ)`, and every source cocharacter `ν`. It invokes
the published `dynamicLeviCocharacterRealization`, retains all three resulting
identities, and adds `NestedParabolicDecomposition ψ χ`. Affineness supplied by
connected reductivity gives the separatedness required by the generic lemma.
No reductivity assumption on `L` is used.

`nestedRealization` chooses such an ambient cocharacter by classical choice.
Its subtype records the three exact realization identities and the full
all-test nested decomposition. It has precisely the field and group hypotheses
of the existence theorem and makes no uniqueness or algorithmic claim.

The provenance is entirely internal: exact-extension inclusions, actual-image
containment, the existing nested decomposition from three inclusions, and the
published simultaneous realization theorem. This adapter supplies structural
inputs for the exact VI.6.2 proof. It does not construct a common maximal split
torus, assert `IsCompatibleNestedPair`, or prove a normalized functor comparison
or finite-length theorem. Those conclusions are absent from its Lean type.
