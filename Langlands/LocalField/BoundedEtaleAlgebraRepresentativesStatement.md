# Finite representatives of bounded-dimensional étale algebras

`Langlands.LocalField.BoundedEtaleAlgebraRepresentativesStatement` starts
with a field \(F\) and a dimension bound \(d\). Its premise is finiteness of
the set of subextensions of \(\overline F/F\) of finite degree at most \(d\).
It asserts that a finite family of \(F\)-algebras represents every étale
\(F\)-algebra of dimension at most \(d\) up to \(F\)-algebra isomorphism.
The family may have repetitions. The étale algebra and the field may
have independent universes.

The comparison uses Mathlib's `Algebra.Etale.iff_exists_algEquiv_prod`
and `IsAlgClosed.lift`. An étale algebra is a finite product of finite
separable field extensions. The dimension bound limits both the number of
factors and each factor's degree. This reduction connects extension
finiteness with conjugacy of maximal tori in the general linear group, as
needed for Renard, § V.2.1, printed p. 104 (PDF p. 110) of the 9 July 2026
edition.
