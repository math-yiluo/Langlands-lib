# Simultaneous approximation of maximal tori at the real places

This proves `SimultaneousRealMaximalTorusApproximationStatement`. A family
of maximal tori over the real completions of a connected reductive group
over a number field is realized by one global maximal torus up to conjugacy
by a rational point at each of those completions.

Choose finite Lie coordinates on the global group and extend them to every
real completion. Each prescribed maximal torus supplies a nonempty open
set of local Lie vectors whose connected centralizer is a conjugate of
that torus. Weak approximation gives one global vector with all its
localizations in those open sets. Its closed centralizer is affine, locally
of finite type, and smooth by Cartier's characteristic-zero theorem.

The Lie centralizer comparison and the identity-component comparison show
that the base change of the connected global centralizer is the connected
centralizer of each local vector. The local conjugacy equations therefore
apply to the base changes of the same global subgroup. Reflection along
any real completion gives the global torus predicate and maximality. For
a number field with no real places, the rational maximal-torus existence
theorem supplies the required torus.

This is the real-place case of Platonov and Rapinchuk, *Algebraic Groups
and Number Theory* (1994), Proposition 7.3, Corollary 3, printed p. 405.
The Lean proof uses the regular Lie slice related to Theorem 2.18, printed
pp. 104–105, and weak approximation for the affine Lie coordinates.
