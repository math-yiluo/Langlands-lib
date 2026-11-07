# Closed envelopes of coordinate translation stabilizers

This is derived supporting work by Worker 1369 for the Steinberg big-cell
construction. It uses the published rational-point closure envelope and actual
affine-coordinate evaluation. It introduces no external source assertion.

Let `k` be a field and `G` an affine group scheme over `Spec k`.
`rationalLeftStabilizer G b` is the subgroup of rational points `h` such that
`b(hg) = b(g)` at every rational point `g`. Here `b` belongs to the actual
coordinate algebra `AffineCoordinates.algebra G`, and evaluation is
`AffineCoordinates.pointAlgebraHom`. Closure under products follows from
associativity; inverse closure follows by evaluating the defining identity
at `h⁻¹g`.

The preliminary lemma `appTop_eq_of_mem_rationalPointClosure` does not need
affineness. If two global functions have equal pullbacks at every rational
point of a set `S`, they have equal pullbacks at every rational point whose
location is in the closure of the locations of `S`. The implemented proof
places those locations in the complement of the basic open of the difference
of the functions. This complement is closed. At a rational point in the
closure, the pullback of that basic open is empty, since the spectrum of a
field has only one point. The source spectrum is reduced, so the pulled-back
difference is zero. This argument uses neither algebraic closedness nor
smoothness of `G`.

For fixed rational `g`, right translation `h ↦ hg` is an actual relative
scheme morphism, supplied by `exists_comp_eq_mul_right`. Pull back `b` by
this morphism and by the constant morphism with value `g`. Their rational
evaluations agree on the rational stabilizer. The preliminary lemma shows
that they also agree at all rational points of its location closure.
`mem_rationalLeftStabilizer_of_mem_closure` therefore proves that this closure
has no additional rational points outside the stabilizer.

Now assume `k` algebraically closed and `G` smooth. Smoothness supplies local
finite type, so the published `LeviGluing.rationalClosureEnvelope` applies to
the rational stabilizer. The definition `leftStabilizerEnvelope G b` is this
actual smooth closed subgroup envelope. Its inclusion has underlying image
equal to the closure of the rational stabilizer's locations.

The theorem `leftInvariant_stabilizerEnvelope` proves
`b(j(h)g) = b(g)` for every relative test scheme `V`, every envelope-valued
`V`-point `h` and every `G`-valued `V`-point `g`, where `j` is the envelope
inclusion. A rational point of the envelope maps to the rational location
closure and hence to the rational stabilizer by the previous theorem.
`AffineCoordinateTranslation.leftInvariant_of_rationalPoints` then upgrades
this rational-pair equality to the asserted equality on every test. Its
hypotheses hold because both `G` and the envelope are smooth; that theorem
uses equality of actual global functions on their reduced product.

The field universe is arbitrary. Relative tests remain unrestricted,
including nonreduced and empty tests. This unit constructs a closed
stabilizer envelope and proves its invariance; it does not prove containment
of root groups, generation, fixed-height restriction injectivity, the
whole induced-space dimension bound, or `SteinbergBigCellStatement`.
