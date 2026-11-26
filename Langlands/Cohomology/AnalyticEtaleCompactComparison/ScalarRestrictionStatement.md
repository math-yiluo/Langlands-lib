# Scalar restriction in analytic étale compact cohomology

`Langlands.Cohomology.AnalyticEtaleCompactComparison.AnalyticEtaleCompactScalarRestrictionStatement`
concerns constant commutative coefficient rings \(R\to S\) and a
Hausdorff space \(X\) analytic over a fixed complete ultrametric normed
field \(K\). A topological group \(G\) acts by \(K\)-analytic
automorphisms with `IsContinuousAction`. Berkovich's original
definition in §1.1 also allows automorphisms of the ground field.

The rings and module carriers have universe `max u (v + 1) uL`. The
instance `Small.{max u (v + 1) uL} G` gives the size of the twisted
site needed for sheafification. The `HasAdmissibleRefinements` instance
for `distinguishedLiftSystem ρ` on `twistedEtaleTopology ρ` supplies the
local action refinement used in the abelian category and its enough
injectives construction. This is the locally discrete twisted-site
model for the smooth sheaves of Theorem 1.4.2.

The normed \(K\)-algebra field \(L\) supplies the chosen points, with
`EtaleSite.PointAxioms L x` at each \(L\)-valued point. The support
condition uses these points with the topology induced by their
projection to \(\lvert X\rvert\). Surjectivity of the projection makes
containment of the support in a compact subset equivalent to
containment of its image in a compact subset of the underlying
space. The relation to Berkovich's geometric-stalk convention is
described in the [compact comparison statement](Statement.md).

For each \(q\) the proposition asserts both natural isomorphisms

\[
\begin{aligned}
\operatorname{Res}_{R}^{S} H_c^q(X\{G\},F)
  &\cong H_c^q(X\{G\},\operatorname{Res}_{R}^{S} F),\\
\operatorname{Res}_{R}^{S} H_c^q(X(G),F)
  &\cong H_c^q(X(G),\operatorname{Res}_{R}^{S} F).
\end{aligned}
\]

Here \(F\) is an actual locally discrete étale sheaf of \(S\)-modules,
and the first isomorphism is in smooth \(R\)-representations of \(G\).
`etaleGSheafRestrictScalars` restricts the module structure of every
section via `sheafCompose`. The same local actions fix the same
sections, so the same covering sieve witnesses local discreteness.
The right sides use the actual compact and invariant compact
cohomology functors of this restricted sheaf. The proposition uses
existence of natural isomorphisms.

Berkovich's *Étale equivariant sheaves on p-adic analytic spaces*
manuscript, Corollary 1.5.2(ii), printed p. 12, compares derived
compact sections in modules over a sheaf of rings with the
corresponding abelian-sheaf cohomology. In the constant-ring case,
one may use this comparison for both \(R\) and \(S\). The underlying
abelian sheaf, supports of sections, and group operators coincide.
The comparison obtained from the Godement resolution in §1.5 is
natural for scalar multiplication and respects the smooth action on
the section complexes. This gives the \(R\)-linear comparison and
the first formula in the smooth category. The scope here is
constant rings with the indicated point-support model.

The manuscript is registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
PDF SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
