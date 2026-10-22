# Contragredient duality on exact virtual representations

This is an internal construction from the published actual finite-dimensional
representation duals in `Langlands.Weil.Representation.Dual` and `DualClasses`,
and the genuine short-exact-relation quotient in
`Langlands.VirtualRepresentation.Exact`. No external source is cited and no
additional arithmetic result is asserted.

The helper `Langlands.FiniteRepresentation.isShortExact_dual` sends an actual
short exact sequence A → B → C to dual C → dual B → dual A, using the published
`Langlands.dualIntertwining` maps. Its coefficient field, group, and three carrier
universes are independent. Pullback of functionals along a surjective map is
injective; along an injective vector-space map it is surjective. Mathlib proves
the latter by extending functionals using a linear left inverse. The range of
the dual of g is the annihilator of ker g, while the kernel of the dual of f is
the annihilator of range f. Original exactness identifies these annihilators.
These are linear-algebra facts, not an assumed equivariant splitting or a
postulated dual exactness theorem. The objects here are finite-dimensional,
although these endpoint and annihilator facts hold more generally over fields.

The remaining construction uses complex coefficients, retaining independent
group and carrier universes. Given a predicate P and explicit closure under the
actual dual, `dualClassWith` maps genuine isomorphism classes to genuine dual
classes. Actual equivalences descend by reversing `dualEquiv`.
`dualClassWith_isExactAdditive` applies the reversed short exact sequence and
commutativity of addition: [dual B] = [dual C] + [dual A] = [dual A] + [dual C].
Thus contravariance on intertwiners still gives a covariant additive endomap on
the quotient. `dual` is the integer-linear map supplied by `Exact.lift`.
`dual_ofClass` and `dual_ofRepresentation` identify its values on genuine classes.
The bidual evaluation equivalence proves `dual_comp_dual` and `dual_dual`, hence
`dualEquivalence` is an integer-linear self-equivalence and its own inverse.
Rank preservation gives `degree_comp_dual` and `degree_dual`; `dualDegreeZero`
is the induced self-equivalence of the kernel of the genuine integer degree.

For any topological group G, `continuousDual` specializes this construction to
P(A) = A.IsContinuous. Closure is supplied by the published
`isContinuous_dual_iff` for the usual complex topology. Consumers provide no
closure or exactness assumption. Named laws describe evaluation on classes and
representations, self-inverse and involution behavior, and degree preservation.
`continuousDualDegreeZero` restricts this same map to the degree-zero submodule;
its coercion, involution, and self-inverse laws are proved. The linear interfaces
supply zero, addition, negation, subtraction, and integer scalar compatibility.
The quotient and all laws include negative virtual classes and nonsemisimple
objects; no irreducible expansion, semisimplification, or inverse realization is
chosen.

The generic topological-group interface can be instantiated at the actual
fixing subgroups `Langlands.LocalFactor.CommonClosure.weilSubgroup F E`, with
carrier universe `max uF uV`, to act on `CommonClosure.Virtual F E`. This module
requires no arithmetic import. It makes no assertion about epsilon functional
equations, Fourier measures, tensor products, determinants, or conductors.
