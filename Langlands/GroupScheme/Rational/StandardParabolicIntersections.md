# Actual intersections of standard parabolics

This internal construction treats a connected reductive group over any field,
an actual maximal split torus, and a generic integral cocharacter. For any two
subsets \(J,K\) of the resulting simple relative roots, it identifies the
scheme-theoretic intersection of the canonical standard parabolics with the
canonical standard parabolic indexed by \(J\cap K\). The field and all group
schemes have arbitrary universe `u`.

`IsParabolicSubgroup.of_smooth_overgroup` first records a general observation.
A smooth closed subgroup containing an actual parabolic is itself parabolic.
The all-test range inclusion gives a homomorphism from the original parabolic
to the overgroup. After base change to the algebraic closure, composing its
base change with the original geometric Borel witness gives the required
Borel witness for the overgroup.

The proof of `standardParabolic_inter` constructs the actual pullback of the
two canonical standard inclusions. The published standard-cocharacter theorem
realizes each standard parabolic as a dynamic parabolic of a cocharacter of
the same split torus. The common-torus dynamic intersection theorem makes
this pullback smooth. It contains the canonical empty-index parabolic, by
the published standard-parabolic order theorem. The preceding observation
therefore proves that this actual pullback inclusion is parabolic.

The published dynamic recognition and standard classification theorems
identify its range with a standard parabolic \(P_I\). The order theorem
then determines \(I\): its two projections give \(I\subseteq J\cap K\), and
the inclusions from \(P_{J\cap K}\) into both factors give the reverse
inclusion. Thus \(P_{J\cap K}=P_J\cap P_K\) as subgroup functors on every test
scheme, including nonreduced tests.

`Standard.parabolicInterIso` applies uniqueness of representatives of a
subgroup functor to this equality. It constructs an actual group-scheme
isomorphism from the canonical standard model for \(J\cap K\) to the pullback
of the two original canonical models. `parabolicInterIso_hom_comp` proves
that its composite with the pullback's original ambient inclusion is
exactly the original standard inclusion for \(J\cap K\).

The provenance is internal composition of the imported Library proofs,
rather than a new translation from the literature. This provides the
intersection step needed when forming families of standard parabolics in
Galois descent arguments. It does not construct a Galois action on such a
family, prove its invariance, establish adelic overlap estimates or root
bounds, or prove adelic compactness.
