# Henselian normalizer lifts negating an actual character

This internal transport unit combines the published exact Henselian normalizer
lifting theorem with the published character lattice comparison for split tori.
It does not identify the lifted normalizer with a relative reflection.

The published `characterAut_baseChange` identifies the character action after
base change with the base change of the original action.
`characterAut_baseChange_eq_neg` reuses that identity to transport a character
negation along any base map. For a split torus over a domain,
`IsSplitTorus.characterAut_eq_neg_of_baseChange` reflects that negation from any
field fibre, using injectivity of the actual lattice base change map.

`exists_henselian_rootNormalizer` starts with a split torus mapping into a smooth
affine group over a Henselian local domain, a surjective map from that domain to a
field, an integral character, and a specified normalizer point and automorphism
over that field. The supplied field automorphism must negate the base changed
character. The theorem gives an integral normalizer with the specified residue
point and automorphism, and proves that its automorphism negates the original
integral character. `henselianRootNormalizerLift` chooses such a pair with all
four properties. The character need not be a root or nonzero.

The implemented proof first uses `exists_henselian_normalizer` to recover the
point and automorphism exactly. The split character lattice comparison then
reflects the character equation. `rootNormalizer_fieldBaseChange` applies the
published base change theorem for the actual normalizing equation and the
character transport lemma to any field over the original ring. Thus the
integral lift has the required generic normalizing equation and negates the
original generic character.

All maps are the actual group scheme maps and lattice maps. No component
membership, generic reflection property, or integral opposite factor conclusion
is asserted here. The provenance is the formal composition of these published
transport and lifting results, rather than a separate assertion from literature.
