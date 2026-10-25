# Generalized matrix coefficients from algebraic functionals

This internal construction packages the existing integrated action, full
transpose smoothing theorem, smooth contragredient, and algebraic distributions.
It is a helper for the Whittaker multiplicity argument, not a multiplicity theorem
or a distribution invariance theorem. No source theorem is being transcribed.

Let \(G\) be a Hausdorff locally compact totally disconnected topological group
with its Borel measurable structure, and let \(\rho\) be a smooth representation
on a complex vector space \(V\). The group and carrier universes are independent.
The measure \(\mu\) is finite on compact sets and right invariant.
There is no topology on \(V\), and no admissibility, irreducibility, unitarity,
or smoothness assumption on the algebraic functionals.

Write \(\pi(f)=\mathrm{Hecke.integratedAction}(\mu,\rho,h_\rho,f)\).
The bilinear map `smoothFunctional` is
\[
 S_\ell(f)(v)=\ell(\pi(f)v).
\]
Its codomain is the existing `SmoothDual ρ`, the smooth-vector submodule of the
full algebraic dual. Membership follows from
`Character.integratedAction_dualMap_range_le_smoothVectors`; linearity follows
from the integrated action and the functional.

For an algebraic functional \(\lambda\) on `SmoothDual ρ`, the bilinear map
`generalizedCoefficient` defines an actual `HarmonicAnalysis.Distribution G` by
\[
 D_{\ell,\lambda}(f)=\lambda(S_\ell(f)).
\]
This uses the existing Schwartz–Bruhat space and the existing definition of
distribution as its complex algebraic dual.

With the Library conventions \(L_a f(x)=f(a^{-1}x)\) and
\(R_b f(x)=f(xb)\), the module proves
\[
 S_\ell(R_bf)=\rho^\vee(b)S_\ell(f),\qquad
 S_\ell(L_af)=S_{\ell\circ\rho(a)}(f).
\]
The second equality additionally assumes left invariance of \(\mu\).
The corresponding distribution equalities transport \(\ell\) and \(\lambda\)
by precomposition with these respective group actions. In particular, under
\(\ell\circ\rho(a)=c\ell\) and \(\lambda\circ\rho^\vee(b)=d\lambda\),
\[
 D_{\ell,\lambda}(L_aR_bf)=cd\,D_{\ell,\lambda}(f).
\]
These are direct consequences of `Character.integratedAction_right_input`
and `Hecke.integratedAction_leftTranslate`; the inverse in the dual action
explains the right-translation formula.

Under left invariance the module also proves
\[
 S_\ell(f*g)=S_{S_\ell(f)}(g),
\]
where the smoothed functional on the right is included in the full algebraic
dual by `smoothDualPairing`. This follows by evaluating
`Hecke.integratedAction_convolution` with \(\ell\).

Finally, when \(\mu\) is Haar measure, `smoothFunctional_eq_zero_iff` proves
that \(S_\ell=0\) exactly when \(\ell=0\). For each vector,
`Hecke.exists_normalizedIndicator_fixes` supplies a normalized compact-open
indicator whose integrated action fixes it. Evaluating the zero smoothing map
at this test function gives \(\ell(v)=0\).
