# Actual cocenter character and coroot comparisons under field extension

This internal supporting module concerns split tori over any field `k` in
universe `u` and any scheme map `b : Spec K → Spec k` for another field in
the same universe. The root-index universes are independent. Neither
algebraic closedness nor finiteness, separability or perfection of the field
extension is required.

For an actual commutative-group homomorphism `f : T → Q`, with both tori
split, `characterLattice.mem_range_precompose_baseChange_iff` says that an
actual character `χ` belongs to the image of pullback by `f` if and only if
its actual base change belongs to the image of pullback by the base-changed
homomorphism. The proof uses bijectivity of character base change for each
split torus and naturality with precomposition. Each extension-field character of `Q` descends uniquely to a character
of `Q` over `k`; the naturality square then reflects the pullback-image
condition. Pullback by `f` is not assumed injective in this lemma.

`characterLattice.pullbackImageBaseChangeEquiv` restricts the canonical
integer-linear character base-change equivalence to the two actual
pullback-image lattices. The image-membership lemma proves that the
restricted source maps onto precisely the target. Its coercion formula
`pullbackImageBaseChangeEquiv_coe` is actual character base change by
construction. This equivalence requires splitness of both tori, but no
injectivity or surjectivity of pullback by `f`.

`characterLattice.precompose_injective_baseChange_iff` proves the matching
invariance of pullback injectivity. It uses the same naturality square:
the two character base-change maps are bijections, so injectivity of either
horizontal map implies injectivity of the other.

For an integral root datum `P` on the actual character and cocharacter
lattices of `T`, and any root-index subset `s`,
`characterLattice.mem_corootAnnihilator_baseChange_iff` reflects and preserves
the selected coroot annihilator under the canonical root datum
`SplitRootDatum.baseChange b T hT P`. This follows from its actual
base-changed coroot formula and its pairing formula. There is no root-span,
reducedness or finite-index hypothesis.

`characterLattice.coroot_character_comparison_baseChange_iff` combines these
facts: injectivity and equality of the actual character image with the
selected coroot annihilator hold over `k` exactly when they hold over `K`
for the canonical transported datum. Surjectivity of character base change
on `T` supplies every extension-field character in the reverse implication.

`SplitRootDatum.map_selected_corootSpan` maps the integer span of selected
coroots to the corresponding transported integer span. It is the submodule
map-of-span identity and the canonical coroot transport formula.
`SplitRootDatum.corootSpan_image_baseChange_iff` treats another split torus
`S`, an actual homomorphism `φ : S → T`, and an integral root datum `R` on
`S`. The equality between the image of the full integral coroot span of
`R` under postcomposition by `φ` and the selected coroot span of `P` is
equivalent to the corresponding equality after canonical base change.
The proof commutes actual cocharacter base change with postcomposition,
uses transport of the full and selected coroot spans, and reflects
submodule equality through the injective cocharacter base-change map.

These are derived algebraic consequences of the published actual split
lattice and root datum base-change constructions; no external theorem is
transcribed. They allow a character or coroot-span comparison for specified
split tori to be verified after a further extension, for example to an
algebraic closure. They do not construct the tori, a compatible derived
torus, root data, an adapted base, or a geometric comparison over the
extension. The cocenter root-model target still needs those geometric
inputs and its based Galois correction.
