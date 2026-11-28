# Compact analytic domain tests for the coefficient action

Take a complete ultrametric extension `L/K`, an affinoid atlas over `K`, and a
topological group acting on `L` by isometric `K`-automorphisms with
norm-continuous scalar orbits. Work in the saturated atlas of the actual
scalar extension. Every chart is represented by a full affinoid domain inside
an extended chart, with its own stored section algebra.

`compactDomainChartCover` chooses a finite cover of any compact analytic domain
by charts contained in it. On each chart, finite rational descent supplies
bounded semilinear operators on the full domain algebra. The intersection of
the corresponding open subgroups is open. `chartFamilySectionMap_chart`
identifies inverse pullback on each chart spectrum with the restriction of the
glued point action. Both the element and its inverse preserve the chart
cover, so the whole compact domain is invariant.

Every chart section has a norm-continuous orbit on this common subgroup.
`eventually_chartFamily_spectralDisplacement_le_ambient` combines the spectral
estimates on the finite cover. It applies to any family of sections on the
cover and hence to the chart restrictions of a section on the compact domain.
The bound holds in an identity neighbourhood of the original group. It is
pointwise on every chart spectrum and simultaneous for any assignment of
positive tolerances to the charts.

These domain invariance and chartwise function bounds supply the local
estimates in Berkovich, *Étale equivariant
sheaves on p-adic analytic spaces* (1995–1996 manuscript), §1.1, pp. 1–2
(printed/PDF), in the coefficient-action case of Example 1.1.1(i). The proof
uses the actual compact chart cover and the bounded semilinear descent on each
full chart algebra. The source is the registered folder
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
with SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The PDF member has SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
