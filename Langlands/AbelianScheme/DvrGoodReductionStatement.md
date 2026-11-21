# Good reduction over a DVR from prime Tate monodromy

`DvrGoodReductionStatement` concerns an abelian scheme \(B\) over the fraction
field \(K\) of a DVR \(V\) of residue characteristic zero. Take a geometric
point \(s\) of \(\operatorname{Spec} K\) and let \(t\) be its image under the
fraction-field map \(j:\operatorname{Spec} K\to\operatorname{Spec} V\). For one
prime \(p\), assume that each element in the kernel of
\(\pi_1(\operatorname{Spec} K,s)\to\pi_1(\operatorname{Spec} V,t)\) acts as the
identity on the actual rational \(p\)-adic Tate module of \(B\). The conclusion
gives an abelian scheme over \(V\) and an isomorphism from its actual generic
fibre to \(B\). The torsion-finiteness premise supplies the covers defining
the monodromy. The prime-power unit witnesses exist in characteristic zero.

This is an adaptation of the good-reduction implication of Bosch,
Lütkebohmert and Raynaud, *Néron Models* (Springer, 1990), §7.4 Theorem 5
(d) implies (b), printed pp. 183–184, PDF pp. 190–191, together with the
existence of the Néron model in §1.4 Theorem 3, printed p. 19, PDF p. 26.
The source tests the integral Tate module on the inertia subgroup for a
chosen strict henselization. Its inertia maps to the identity over \(V\)
because finite étale covers split over the strict henselization. The
integral Tate module injects into the rational Tate module. These
comparisons explain the use of the rational representation and the kernel
condition in the Lean formulation. The argument only needs the inclusion of
the chosen inertia subgroup in that kernel.
Registered source `bosch-lutkebohmert-raynaud-1990-neron-models`.
