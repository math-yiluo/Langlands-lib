# Relative Levi conjugacy from etale-local radical conjugators

Worker 593, using Worker 639's arbitrary-test uniqueness lemmas.

This internal derived unit connects the conjugator predicate, the conjugated
range over a test scheme, algebraic uniqueness, and etale descent.
`EtaleLocallyRadicalConjugate l l' r T` means that an etale cover of the
actual scheme underlying `T` has radical points which conjugate the two
ranges after every further test-scheme restriction. The cover index universe
is a parameter. This definition supplies no local witnesses.

The comparison `rangeConjugateAt_radical_image_eq` uses naturality of the
actual pullback-point equivalence under `r`: lifting a point's image is
the same as lifting the point and then applying the pulled-back inclusion.
Consequently `IsRadicalConjugator l l' r n` is equivalent to equality between
the pulled-back range of `l'` and `radicalConjugateAt l r T n`. This comparison
requires no geometric or monomorphism hypotheses.

Equality of two such conjugated ranges gives equality of the points by
`radicalConjugateAt_injective_of_range_le`. Its premises remain explicit:
monicity of `l` and `r`, a multiplication isomorphism for `l` and a subgroup
`s`, containment of `range r` in `range s`, and containment of the all-test
normalizer of `range l` in `range l`. The relative version instead assumes
the entire propositions `RelativeUnipotentRadicalStatement` and
`RelativeLeviSelfNormalizerStatement`, together with the stated reductive,
relative parabolic, radical and Levi predicates. It uses the corresponding
conditional arbitrary-test injectivity theorem.

The general descent theorem applies this uniqueness on every test scheme
to the existing effective-epimorphism gluing theorem. Monicity of `l'` is
also assumed, as needed for etale locality of its range. Local points agree
on overlaps by uniqueness, glue as actual scheme morphisms, and satisfy the
conjugator predicate by locality.

Finally, for two relative Levi subgroups, closedness gives both required
monomorphisms. Gluing over an etale cover of the base gives a unique base
section satisfying the all-test predicate. The base-section comparison
rewrites that predicate as the exact subgroup-range equation appearing in
`RelativeLeviConjugacyStatement`.

The result is conditional: the two geometric statements and etale-local
existence of radical conjugators remain inputs. In particular this module
does not prove the unchanged unconditional conjugacy target. The provenance
is internal composition of the categorical comparison, arbitrary-test
injectivity and effective-epimorphism descent results; it introduces no new
geometric assertion or axiom.
