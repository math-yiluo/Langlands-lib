# Nonzeroness and endpoint extraction for represented induction

This module gives internal supporting proofs for the represented maximal-Levi
length-two interface of Renard VI.5.4 and VII.1.3. It does not prove the
represented length bound.

`leviInduction_nontrivial` proves that the published actual normalized induction
from `M(k)` is nonzero on a nonzero smooth representation. It needs only a field
with a Hausdorff topology, an affine ambient group whose point group is locally
compact and nonarchimedean, and the actual parabolic/Levi/radical multiplication
data. It does not need maximality, irreducibility, supercuspidality or a
central character. The proof uses the published `continuous_projection_pointImage`
from `ArbitraryParabolicInductionAdmissibility`. This identifies the actual
semidirect-product projection with the point map of the algebraic Levi
retraction, and proves its continuity. The radical image is closed by the
published `isClosed_pointImage_comp`. The published
`nontrivial_normalizedInduction` from `RationalStandardInductionNonzero` then
applies to the pullback of the inducing representation along the inverse of
`leviPointsEquiv`. This pullback has the same carrier. The generic nonzeroness
proof constructs compactly supported local sections whose evaluation at the
identity is any prescribed vector; it does not require quotient compactness.

`maximalLeviSupercuspidalLengthTwo_of_lengthBound` proves the implication from
`MaximalLeviSupercuspidalInductionLengthBoundStatement.{u,v}` to
`MaximalLeviSupercuspidalInductionLengthTwoStatement.{u,v}`. It installs exactly
the field, ambient and Levi topologies and instances used by those statements.
Irreducibility makes the inducing carrier nontrivial. The preceding theorem
makes the actual induced carrier nontrivial. The published
`SmoothRep.exists_two_irreducible_factors_of_length_le_two` in
`LengthTwoExtraction` applies to the length bound and reducibility, and returns
actual irreducible endpoints and a short exact sequence. Its intertwiners are
bundled as smooth-representation morphisms. All induced and endpoint carriers
remain in `max u v`, with `u` independent of `v`.

This is a proved reduction with an explicit unresolved length-bound premise,
not an unconditional proof of either the represented length bound or the
unitarizable-constituent target. Its source motivation is Renard, French version
of 9 July 2026, VI.5.4 (PDF pp.179–180) and VII.1.3, equation (VII.1.3.2)
(PDF p.231). The implemented proof reuses the Library's general local-section
and module-length arguments rather than Renard's Jacquet-module computation.
