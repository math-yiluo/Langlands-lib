# Geometric reducedness of rational-point closures

This internal prerequisite for positive-power factorization strengthens the
published rational-point closure construction over an arbitrary field.
It imposes no perfection or algebraic closedness assumption.

`SmoothCommutativePointEnvelope G x` records a commutative group scheme, its
closed inclusion into `G`, an actual `rationalPoints` point mapping to `x`,
and smoothness and affineness. The constructor
`smoothCommutativePointEnvelope` assumes that `G` is affine and locally of
finite type; smoothness of the ambient group is unnecessary.

The quotient coordinate algebra of `RationalPointClosure` is separated by its
rational evaluations (`eq_zero_of_forall_lift`). The first lemma transfers this
separation to global sections of its spectrum using the naturality of
`Scheme.ΓSpecIso`. Tensoring this family of maps with a field point preserves
joint injectivity by `ImageGeneration.appTop_tensorHom_eq_zero`. The images of
nilpotents vanish because the corresponding base changes of `Spec k` are
reduced. Thus every field base change of the closure is reduced.

The constructor takes the closure of the integer powers of the point.
`RationalPointClosure.isCommMonObj_closure` proves its commutativity on every
scheme test, including nonreduced tests. The closed immersion inherits local
finite type from `G`; Mathlib's `AlgebraicGeometry.smooth_of_grpObj` then gives
smoothness from geometric reducedness. The spectrum of the base algebra is
identified with the unit test object by an explicit isomorphism, so the
returned point uses exactly the Library's `rationalPoints` convention.

This is a derived argument using the current Library's coordinate closure and
tensor separation results. It implements the schematic-density route behind
Milne, *Algebraic Groups* (2017), corrected 1.45/1.48 and 1.26; it does not use
the invalid product-topology argument identified by the erratum to 1.40.
