# Natural support filtration of smooth induction

Authors: Worker 164 and Worker 14. This internal construction adapts the
published compact-induction support construction by Worker 14 to the existing
smooth-induced function model. It imports that module's actual orbit data and
initial-union identities. It introduces no external mathematical assertion.

For any commutative coefficient ring, topological group G, and subgroups P and
Q, `rawRestrictedSmoothInduction P Q` smoothly induces arbitrary algebraic
P-representations to G and restricts the resulting right translation action to
Q. The covariance representation need not be smooth. The function carrier has
universe `max uG uV`, with coefficient, group, and input carrier universes
independent.

`rawSmoothSupportSubfunctor P Q U hU` consists exactly of those smooth induced
functions whose nonzero support projects into the right Q-invariant subset U
of the actual quotient P \ G. Pointwise addition and scalar multiplication
preserve this condition. Translation invariance follows by applying hU to the
inverse translating element. Intertwiners act by postcomposition and cannot
increase support, proving naturality.

`OrderedDoubleCosets.rawSmoothSupportFiltration` uses the specified initial
orbit unions as support sets. The filtration is monotone by containment. Its
initial step is zero because a function supported in the empty set vanishes
pointwise; its last step is full because the orbits cover the quotient. The
construction uses the existing representative convention P w^-1 and retains
the specified ordering. Although OrderedDoubleCosets includes disjointness and
openness, these elementary endpoint proofs need only invariance, monotonicity,
and the cover.

This supplies a support filtration for the smooth-function model used by
normalized parabolic induction without first comparing it with compact
induction. No orbit ordering is constructed here. Compactness of parabolic
quotients, exactness of Jacquet localization, graded-piece isomorphisms, and
the normalized geometric lemma remain separate obligations. In particular,
this module makes no claim that the smooth and compact induction functors
agree, or that these smooth support quotients are compact orbit pieces.
