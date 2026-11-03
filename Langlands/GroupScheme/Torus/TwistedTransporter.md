# Twisted transporter actions and nilpotent lifting

This internal construction packages a transporter between two actual
homomorphisms of group schemes as the fixed locus of a scheme action. The action
exists for any acting group scheme. Its lifting theorem specializes to a
diagonalizable acting group over any commutative base ring, with any additive
commutative character group in the same universe. The target group scheme is
affine and its coordinate algebra is assumed formally smooth.

`PointwiseSchemeAction.twistedTransporter i₁ i₂` uses the actual morphism on `H × G`
given by `(h,g) ↦ i₁(h) g i₂(h)⁻¹`. Its identity and associativity laws follow
from the two homomorphism laws and the target group laws.
`twistedTransporter_act` states the resulting formula on arbitrary test schemes.
Preservation of the target group law is not required by `PointwiseSchemeAction`.

`IsTransporter i₁ i₂ g` requires `i₁(h) g = g i₂(h)` after every refinement of
the test scheme and for every acting point on that refinement.
`twistedTransporter_isFixed_iff` identifies this condition with all-refinement
fixedness for the constructed action by multiplying the inverse term across the
equality. No restriction to rational points or to affine refinements is made.

`exists_transporter_lift` applies `PointwiseSchemeAction.exists_fixed_lift` to this action.
For a nilpotent ideal `I` in an algebra `C`, every transporter point over `C/I`
lifts to a transporter point over `C`, with its reduction equal to the original
point as an actual scheme morphism. The result applies to arbitrary pairs of
diagonalizable homomorphisms; neither a closed immersion nor an automorphism
assumption is needed. It does not identify every normalizer point with a twisted
transporter or assert a geometric smooth representative.

The provenance is the internal group-law calculation and the imported
fixed-point lifting theorem. No additional literature theorem is used. The
unchanged graded helper behind lifting retains Worker 1131's contribution to the
original rank-one square-zero argument.
