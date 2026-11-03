# Filtered colimits of actual relative scheme points

This target gives the generic fixed-model comparison used in Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (31 December 2011), printed
pages 5–6, Theorem 3.4(1) and Remark 3.5, especially the fixed-model expression
in (3.5.1) and its bijectivity argument. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
These original pages were read for this target; no registered errata file was
present at the workspace's Library base.

`FilteredRingPointComparison` is a proposition, with no proof supplied here.
It quantifies over any commutative base ring `R`, any small filtered category
`J`, any diagram `F : J ⥤ CommAlgCat R`, an algebra cocone `c` with an actual
colimit witness `IsColimit c`, and any scheme `X` over `Spec R`. All carriers,
scheme sizes and index-category sizes are in one arbitrary universe. The
actual point carrier is `RingPoint R X A`, namely morphisms from `Spec A` to
`X` over `Spec R`. The quotient and comparison are exactly `RingPointColimit`
and `ringPointColimitMap` from `FilteredRingPoints`; the stage maps are the
actual precomposition maps `RingPoint.changeRing`.

The first implication assumes only `LocallyOfFiniteType X.hom`. It asserts
injectivity of the comparison and two explicit eventual-equality criteria.
Points from any two stages have equal images over `c.pt` if and only if
there is a common later object with transition arrows from both stages on
which they agree. For two points of the same stage, one transition arrow
suffices for both points. This includes the converse implications, so the
criteria identify the actual equality relation, rather than only giving an
existential consequence of equality.

The second implication assumes `LocallyOfFinitePresentation X.hom`. Every
actual `c.pt`-valued point then comes from an actual point at some stage,
with the stated equality after change of value algebra. It also asserts
surjectivity and bijectivity of the same canonical comparison. There is no
assumption that `X` is affine, quasi-compact, quasi-separated or separated.
There is no topology, locality, Noetherianity, injectivity of algebra maps,
or arithmetic hypothesis on the value algebras.

The source gives a finite-presentation theorem for varying base-changed
models and applies it to (3.5.1). The present fixed-target formulation and
its weaker equality-descent hypothesis are a derived generalization, not
an assertion that Conrad stated the locally finite-type version verbatim.
A proof route is available in pinned Mathlib's
`Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`:
`Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`, its two-stage
variant, and `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`.
Relative spectra give quasi-compact, quasi-separated source schemes and
affine transition maps; `ringTestConeIsLimit` supplies their actual limit.
Mathlib's `Scheme.preservesColimit_yoneda` packages the finite-presentation
case, and its filtered type-colimit equality criteria match the explicit
stage comparisons. These proved inputs explain the proposed generality;
this statement file itself does not establish the comparison.

This target does not cover existence of a model over an earlier ring,
comparisons of two varying models, descent of scheme properties, the
arithmetic realization of the diagram by the actual local or adelic rings,
or any topology or model independence of adelic points. Those obligations
from Theorem 3.4 and Remark 3.5 remain separate. In particular, no whole-paper
or complete arithmetic version of (3.5.1) is claimed by this target.
