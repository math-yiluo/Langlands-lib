# Monomorphisms descended from identical all-test fibers

Worker 708. This is an internal fpqc descent argument, valid over any base
scheme `S : Scheme.{u}`.

Let `q : X → Q` be a flat, surjective, quasi-compact relative scheme map and
`r : X → R` another actual relative map. Suppose `q` and `r` have identical
fibers on every relative test scheme. The existing effective-epimorphism
descent constructs `d : Q → R` with `q ≫ d = r`.
`mono_desc_of_fiber_iff` proves that the underlying scheme map of `d` is a
monomorphism. No covering property is required of `r`.

The helper `hom_ext_of_local_lift` pulls back `q` along a test point `x`.
The resulting projection is fpqc and hence an epimorphism, so equality of
relative maps can be tested after that pullback. This is the generic form
of the local-lift argument already used by the Library's flag quotient
action. The monomorphism proof applies this helper twice to lift both
points of `Q` locally. Equality after `d` then gives equality after `r` of
their lifts; the all-test fiber equivalence gives equality after `q`.
The two epimorphism cancellations return equality on the original test.
Finally `Over.mono_left_of_mono` gives the underlying scheme monomorphism.
Tests may be nonaffine, nonreduced or of arbitrary type.

This supplies only a monomorphism. It establishes neither closedness nor
properness of this morphism or its source. In particular an fpqc
projection and identical fibers do not by themselves make `d` closed.
