# Complete compatible strong projections from the small fibre-product atlas

This internal construction retains all admissible bounded pullbacks for the
actual same-universe fibre-product atlas. Quotient smallness and saturation
of all three original atlases are explicit; the field universe is independent
of the common space and index universe.

`smallRep` recovers the original good pair underlying each shrunk chart-domain
index. Its affinoid algebra and spectrum points are unchanged. `small_chart`
gives the literal chart formula through the canonical quotient homeomorphism,
and `small_chart_subset` recovers original quotient chart containment.

`smallFstBase` and `smallSndBase` conjugate the actual quotient projections by
the inverse canonical shrinking homeomorphism. Their chart equations retain
the actual original bounded left and right pushout legs. For every admissible
original target chart, `smallFstPullback` and `smallSndPullback` change that leg
to the target chart using the existing bounded chart-change operation.

`smallFstHom` and `smallSndHom` are complete compatible strong maps. The source
restrictions are the original pair range restrictions transported through the
homeomorphism and index equivalence. Naturality follows because the two sides
are chart changes of the same original leg. The existing chart-change
coherence theorem proves compatibility for all admissible target pairs.

These constructions assume an actual small quotient; they do not prove that
an etale leg supplies it. Saturated-category extension, the commutative square,
complete cone universality and etale base change remain further work. No
external statement is transcribed.
