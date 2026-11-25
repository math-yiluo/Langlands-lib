# Proof that invariant analytic domains of `G`-spaces are `G`-spaces

The theorem `invariantDomainContinuity` in this module has exactly the type
`InvariantDomainContinuityStatement.{u, v, w, z}`, the statement published in
`Langlands.Geometry.Analytic.InvariantDomainContinuityStatement`. Its universe
parameters are those of the statement: `u` for the field `K`, `v` and `w` for
the space and the charts of the analytic space, and `z` for the group `G`.

## Statement proved

Let `K` be a complete ultrametric normed field, `G` a group with a topology,
`X : GSpace K G` a `G`-space, `D` an analytic domain of the saturated
presentation of `X.obj.V`, and `hD : IsInvariantDomain X.obj D` (every element
of `G` maps `D` into itself). Then the action of `G` on `D` by restricted
automorphisms, `(invariantDomainAction X.obj D hD).ρAut`, satisfies
`IsContinuousAction`.

## The implemented proof

The proof is one term. A `G`-space is an object of the full subcategory for
`gSpaceProperty K G`, so `X.property` is the conjunction
`T2Space (localizedSpaceFunctor.obj X.obj.V) ∧ IsContinuousAction X.obj.ρAut`.
Its second component, `X.property.2`, is the continuity of the action on `X`.
The proof applies the published Library theorem
`IsContinuousAction.invariantDomainAction` (module
`Langlands.Geometry.Analytic.ContinuousInvariantDomain`) to this continuity
proof, to `D` and to `hD`. That theorem concludes
`IsContinuousAction (invariantDomainAction X.obj D hD).ρAut`, which is the
required conclusion. The Hausdorff component of `X.property` is not used.

`IsContinuousAction.invariantDomainAction` is proved in the Library as follows.
For a test triple `τ` of the domain, `τ.ambient` (module
`Langlands.Geometry.Analytic.StrongNearDomainTransport`) is the test triple of
`X` with the same chart, function and bound. By continuity of the action on
`X`, the set of `g` with `IsNear τ.ambient (X.ρ g) (𝟙 X)` is a neighbourhood of
`1` in `G`. For every such `g`, `IsNear.domainRestrict_id` (module
`Langlands.Geometry.Analytic.NearIdentityDomainRestriction`) gives
`IsNear τ (domainRestrict D D (X.ρ g) (hD g)) (𝟙 (domainObj X.obj.V D))`, that
is, the restricted automorphism lies in `nearIdentity τ`. So the preimage of
`nearIdentity τ` under the restricted action contains a neighbourhood of `1`,
and is itself a neighbourhood of `1`.

This is the argument recorded in the statement's Markdown: a test triple of
`D` is a test triple of `X` whose chart lies in `D`, and a group element near
the identity for it on `X` stays near the identity on `D`.

## Checks

A Lean check (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) on Library base
`ecb96e554fed652972a5c0308d69b041f6bc54e4` compiles the module with no errors
or warnings. The theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. The statement module and the modules it
imports are unchanged.

## Sources

Continuity of actions and `G`-spaces are Berkovich's: *Étale equivariant
sheaves on p-adic analytic spaces* (unfinished manuscript, 1995–1996),
registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.1, printed pp.1–2. The manuscript uses the proved property without comment
in §1.4, printed p.7. The proof above follows the Library's own argument, which
is derived and not taken from a source.
