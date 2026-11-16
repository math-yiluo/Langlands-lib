# Actual local rank-one reflection and normalizer squares

This is an internal prerequisite for the local split Isomorphism Theorem.
It is derived from the published all-test-scheme self-centralization of
fibrewise maximal split tori, normalizer composition, and the explicit
reflection in the ring root-cell calculus.

`IsNormalizingPoint.exists_sq_eq_of_fibrewiseMaximal` applies over an
arbitrary scheme. It assumes a reductive ambient group, a closed split torus
whose fibres are maximal, and a normalizing section whose specified torus
automorphism squares to the identity. Composing the normalizer with itself
shows that its square centralizes the torus. The published equality of the
torus centralizer with the actual torus range then supplies an actual torus
section mapping to that square.

`RingRootCell.reflectionIso_trans_self` checks the required involutivity for
the explicit reflection `1 - α ≫ h`. Its hom and inverse are definitionally
equal, so its own inverse law gives the result. The assumption is the actual
morphism identity `h ≫ α = 2 • 𝟙`, with no reducedness premise.

`LocalRankOneWeylData.coroot_comp_root` uses a supplied full fibrewise root
datum over a commutative local ring. Its pairing on the residue field
identifies the coordinate pairing with the integer dot product, and the
root-coroot axiom makes that dot product two. The fixed-exponent composition
formula then proves the actual morphism identity over the whole base.

`LocalRankOneWeylData.reflectionIso_eq_exponentCommIso` identifies the
ring-calculus reflection with the actual exponent automorphism of the
coordinate root reflection. The proof compares pullback on fixed-exponent
characters, uses their integral linearity and the same dot-product formula,
and concludes by the coordinate projections of the split torus.

`LocalRankOneWeylData.corootReflectionIso` packages this actual automorphism
from the supplied root, coroot and the proved composite identity. It is
definitionally the ring-calculus reflection and equals the coordinate
exponent reflection by `reflectionIso_eq_exponentCommIso`.

These are preparation lemmas. They do not construct a normalizing section,
its open-cell decomposition with unit coordinates, or `RingRootCell.WeylData`.
The full local Isomorphism Theorem remains open.
