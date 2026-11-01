# Finite relation loci for a restricted represented ring presheaf

Let `C` be a category with the indicated finite products and equalizers, let
`R : Cᵒᵖ ⥤ RingCat` be a ring-valued presheaf, and let `P` be an object
property defining a full test subcategory. Supply an object `E` and a natural
isomorphism `e` from the underlying set-valued presheaf of `R`, restricted to
that full subcategory, to the correspondingly restricted Yoneda presheaf of `E`.
Also supply a ring `O` with a finite integer basis `b`, indexed by `I`.

The construction assumes explicitly that `P` holds for the actual product
`E^I`. It does not assume closure of `P` under finite products or require `P`
of the equation product or of the output locus. For example, when `P` means
local noetherianness, this finite-power premise is a genuine additional input.

`EquationIndex I` is the finite type `Unit ⊕ (I × I)`. For a tuple `r` in any
target ring, the two equation functions have values

| Index | `equationLeft b r` | `equationRight r` |
| --- | --- | --- |
| Unit | `Σ_i b.repr(1)(i) • r_i` | `1` |
| Ordered pair `(i,j)` | `Σ_k b.repr(b_i b_j)(k) • r_k` | `r_i r_j` |

Here the coefficients are integers acting by the canonical additive scalar
action. Multiplication in the target ring can be noncommutative, so every
ordered pair is retained. `relations_iff_equations` identifies equality of
these components with the published finite ring-action relation predicate,
including for zero rings and empty bases where the supplied hypotheses allow
them.

`tupleEquiv` identifies maps from a test object to `E^I` with tuples in its
`R`-value, by applying `e.inv` to each projection; its inverse uses the product
lift of the maps given by `e.hom`. The inverse laws follow from those of `e`
and the product. `tupleEquiv_comp` proves compatibility with every morphism
in the full test category.

Using the explicit premise `P(E^I)`, `universalTuple` decodes the identity
morphism of this finite power. `equationLeftHom` and `equationRightHom` apply
the two equation functions to that tuple and encode the components by `e.hom`,
giving two actual morphisms from `E^I` to `E^(EquationIndex I)`.
Naturality of `e` proves that restricting the universal tuple along any
test morphism gives its decoded tuple. Since each restriction of `R` is a
unital ring homomorphism, it preserves the integer-linear sums, unit and
ordered products. The two decode theorems therefore identify the components
of these actual morphisms with the stated ring equations on every test.

`equation_hom_condition_iff` uses product extensionality and injectivity of
`e.inv` to identify equality after these two morphisms with precisely the
finite relation predicate. `locus` is their actual categorical equalizer.
Its universal property and the tuple equivalence give `locusHomEquiv`,
identifying maps into the locus with the solution subtype. The inverse is
the equalizer lift of the reconstructed tuple map; the inverse laws follow
from the equalizer inclusion and the tuple inverse laws.

`locusSolutionsIso` packages this equivalence naturally on the entire full
test category. `actionLocusIso` composes its inverse with the published
natural comparison from unital ring homomorphisms `O → R(T)` to solutions.
Thus it constructs an actual representing locus relative to these tests,
given the specified `E`, `e` and finite-power hypothesis.

The object universe of `C`, its Hom universe, and the universes of `I` and `O`
remain independent. The ring carriers have the Hom universe, as required by
the supplied unlifted comparison with Yoneda. The output uses
`uliftYoneda.{max uI uO}` and the existing lifted solution/action functors,
with explicit canonical lift equivalences matching their common universe.

The provenance is internal: finite products, equalizers, naturality, and the
published finite-basis ring-action equivalence imply the construction. No new
literature assertion or representation premise beyond the displayed inputs is
used. In particular the module supplies no existence proof for `E` or `e`,
no geometric property of the locus, and no passage from rational actions to
integral actions or normalized moduli classes.
