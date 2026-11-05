# Compact-domain Poincaré periodization and absolute Fubini

`Langlands.QuotientIntegration.CompactPeriodPoincareStatement` is an
internal analytic construction target for the compact-period Poincaré
argument. It is a proposition definition, not a proof.

Let `G` be a locally compact Hausdorff second countable Borel topological
group and `Γ` a closed subgroup. Its actual measure `μΓ` is s-finite,
right invariant and finite on compact sets. Let `X` be a locally compact
Hausdorff second countable Borel space, with an actual measure `μ` finite
on compact sets. Let `s ⊆ X` be measurable with compact closure, let
`j : X → G` and `w : X → ℂ` be continuous, and let `f : C_c(G, ℂ)`.

The joint integral

\[
 \int_{\Gamma\times s}
   |w(x)f(j(x)^{-1}\gamma g)|\,d\mu_\Gamma(\gamma)\,d\mu(x)
\]

is finite for every `g`. Consequently the actual orbital average of
the compact-domain test function satisfies

\[
 A_\Gamma\!\left(g\mapsto\int_s w(x)f(j(x)^{-1}g)\,d\mu(x)\right)(q)
 =
 \int_s w(x)\,A_\Gamma\!\left(g\mapsto f(j(x)^{-1}g)\right)(q)\,d\mu(x).
\]

The target states joint absolute convergence as `Integrable` for the
product of `μΓ` and `μ.restrict s`, and uses the existing actual
`quotientAverage` on the left-coset quotient `Γ * g`. Right invariance
of `μΓ` makes those orbital averages descend. No normality,
commutation of `j(X)` with `Γ`, fundamental-domain hypothesis or finite
total volume is imposed. Both spaces have independent universes.

## Source and remaining work

Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
§9.2, printed pp.244–245, one-based PDF pp.256–257, equations
(9.8)–(9.11) and Lemmas 9.2.4–9.2.6, forms a compact-domain test function
and interchanges its period integral with rational periodization.
This target is the continuous general closed-subgroup integral version
of that step. In the source application, `μΓ` is counting measure on
rational points, `X` is the period group, `j` is its inclusion, `s` is
a relatively compact measurable fundamental domain, and `w=χ⁻¹`.
The complete October 2026 errata corrects the period quotient after
(9.9) and the character/modular factor in Lemma 9.2.6.

The separate compact-domain test construction supplies the compact
continuous function inside the left-hand side. This target does not
select a fundamental domain, construct the quotient period measure,
prove smoothness, introduce the modular correction in the subsequent
L² pairing identity, prove period test separation, or establish
cuspidal closedness. An independently reviewed exact-target proof and
the actual adelic specializations remain required.
