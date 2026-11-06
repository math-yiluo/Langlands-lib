# Homomorphisms from split tori to anisotropic affine groups

Author: Worker 1326.

`IsAnisotropic.hom_eq_zero_of_isSplitTorus` states that any homomorphism
from an actual split torus to an anisotropic affine group scheme is the
trivial homomorphism. The field `k : Type u` and universe `u` are arbitrary.
The target need not be smooth, connected, reductive or commutative, and the
homomorphism need not be a closed immersion.

The proof is an internal consequence of the published split-image theorem
`IsSplitTorus.exists_factor_isSplitSubtorus` in `Rational.SplitTorusImage`
and the published rank-zero corollary
`IsAnisotropic.subsingleton_hom_of_isSplitSubtorus` in
`Rational.SplitTorus`. Factor the given map through its closed split-torus
image. Anisotropy makes all homomorphisms from that image to the target
equal, so its inclusion equals the trivial homomorphism. Composing with the
image projection proves the claim.

`IsAnisotropic.comp_hom_eq_one_of_isSplitTorus` evaluates this equality on
an arbitrary test scheme. It includes nonreduced tests and asserts no
surjectivity on field-valued points.

`IsAnisotropic.uniqueHomFromSplitTorus` constructs `Unique (T.toGrp ⟶ G)`,
with the trivial homomorphism as its canonical default and the preceding
vanishing theorem as its uniqueness proof.

This derived helper supplies the split-torus-image step in the proof of
`SimplyConnectedAnisotropicFactorCentralizerStatement`. It does not assert
existence of a normal complement or retraction in a simply connected
semisimple group.
