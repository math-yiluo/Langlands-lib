# Actual local coroot quotients from the negative-simple cell law

This internal unit constructs the actual local torus quotient needed by
the relative derived-group existence argument. The input is a reductive
group scheme `G` with affine structure morphism over any commutative local
ring `R`, a closed coordinate split torus `i` maximal on every field fibre,
and a fibrewise root datum `P` for `i`. The finite coordinate type has
decidable equality. No reducedness, noetherian, henselian, characteristic
or residue-field hypothesis is imposed on `R`.

`RelativeDerived.localCorootQuotient` is an actual chosen homomorphism
from `G` to the split torus `corootQuotient R P`, packaged with its exact
restriction `i ≫ q = corootProjection R P`, smoothness and surjectivity.
`exists_localCorootQuotient` proves the corresponding existence theorem.
The target is the diagonalizable torus of the integral character lattice
annihilating every coroot.

The first step discharges the negative-simple cell law.
`corootCellProjection_eq_of_negativeSimple_relation` allows any supplied
family parametrizing all roots, arbitrary enumerations of negative and
positive roots, a simple root `a`, and any other parametrization `v` of
`-a`. For every relative scheme test and arbitrary scalar `c`, an equality
`cell(x) * v(c) = cell(y)` implies equal values of the coroot cell
projection. Thus this assertion retains all scheme-valued information,
including nilpotents.

The translating parametrization need not equal the family's selected
negative-root parametrization. `IsRootParametrization.exists_rootPoint_eq`
uses equality of their full represented root subgroup ranges to express
the translating point in the family's coordinates. It uses the actual
additive-group coordinate of the resulting point and requires no
comparison by field points or classification of additive automorphisms.
The root enumerations select positions for `a` and `-a`. The fibrewise
root datum gives the explicit coordinate-dot-product pairing, and
`cellRankOnePart_mul_negativeSimple_of_cell_relation` extracts a literal
rank-one relation with the original torus coordinates.
`rankOneQuotientLaw_corootProjection` then proves equality of the quotient
values. This last theorem is applied to the actual opposite root maps,
with no supplied Bruhat or denominator-unit premise.

`negSimpleRelations_corootCellProjection` applies that all-test result
to the Weyl family and to the original simple-root data. Its target root
maps are trivial. Although the generator-relation interface tests local
rings with separably closed residue fields, the preceding invariance
lemma is stronger and needs no such restriction on its test schemes.
The same-range point comparison handles any difference between the
original negative-simple map and the Weyl family's map.
`cellCompatible_corootCellProjection` combines this result with the
previously proved positive-root and torus laws, discharging every
premise of the generator-relation gluing argument.

For existence, the fibrewise root datum supplies finite reduced root
data and a base. `exists_normalizedLocalRootFamily` constructs actual
root parametrizations with the simple pairs Weyl-normalized over `R`.
The proof chooses simple reflection words and finite root enumerations.
The resulting Weyl family has an open big cell by the published local
big-cell theorem. The compatibility theorem just proved allows
`smoothCorootCellExtension` to glue the actual group homomorphism from
the coroot cell projection. That construction gives exactly the torus
restriction, smoothness and surjectivity stated here. The final
`localCorootQuotient` selects this proved witness and retains all three
properties in its subtype.

This construction proves the local coroot quotient without additional
mathematical inputs. Passing to arbitrary bases, identifying the full
geometric kernel and completing the unchanged relative derived-group
existence theorem are separate steps.
