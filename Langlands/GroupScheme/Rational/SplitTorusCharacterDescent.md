# Character descent from pointed split-torus domination

Worker 1376 constructs the character equivalence; Worker 1485 supplied the
group homomorphism descent adapter used in its proof. This is an internal
derivation from the Library's pointed-morphism rigidity, split-torus lattice
base change, actual affine descent and faithful pullback. No original source
assertion is transcribed.

Let `k` be a field, `H` a reduced affine group scheme over `k`, and suppose
`HasPointedSplitTorusDomination H`: there is an actual pointed dominant scheme
morphism `p : P.X → H.X` from a split torus `P` over `k`. Both field carriers
may lie in any common universe `u`. For every field extension `K/k`,
`HasPointedSplitTorusDomination.characterEquiv` is an additive equivalence
between the actual rational characters of `H` and those of its actual scalar
extension `H_K`. Its forward map is exactly `rationalCharacters.baseChange`,
using the canonical comparison `(Gm_k)_K ≅ Gm_K`. Its inverse is a character
defined over `k`, and `baseChange_characterEquiv_symm` proves recovery of the
given character. Injectivity of the original base-change map proves uniqueness.
No smoothness, connectedness, solvability, finite-type, characteristic,
perfectness, infinitude, algebraicity or separability hypothesis is added.

The proof first establishes `IsSplitTorus.exists_character_of_pointed_composite`:
for any pointed scheme map from a split torus, composing its scalar extension
with a character is a pointed morphism between tori. The Library's
`IsTorus.homOfPointedMorphism` makes this actual morphism a homomorphism, and
`IsSplitTorus.characterLattice_baseChange_bijective` gives a character of the
source torus over `k`. This first step requires no dominance.

For `HasPointedSplitTorusDomination.exists_character`, the source split torus
is affine. Dominance into the reduced affine target makes the actual coordinate
pullback injective: the scheme map is quasi-compact and schematically dominant.
After composing the extension-field character with the inverse canonical
multiplicative-group comparison, the composite equality from the first step
is precisely the hypothesis of `AffineEmbeddingHomDescent.existsUnique_hom`.
That adapter descends an actual affine scheme morphism, recovers its scalar
extension, and reflects the group laws through faithful monoidal pullback.
Composing back with the multiplicative-group comparison proves recovery of
the original character. The result is an equality of actual group-scheme
morphisms, hence holds on all scheme tests.

`character_baseChange_bijective` combines this surjectivity with the existing
injectivity under field extension, and `characterEquiv` packages that map as
an additive equivalence. Finally, `transportCharacter_eq` proves that every
extension-field character is fixed by canonical descent transport along any
endomorphism of `Spec K` over `Spec k`: write the character as a base change
and apply `rationalCharacters.transportCharacter_baseChange`.

This helper does not construct a torus quotient or its unipotent kernel, prove
kernel smoothness or connectedness, or establish the final split geometric
radical theorem. Those remain separate proof obligations of the host task.
