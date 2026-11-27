# Analytic levels and Hecke maps of the represented Harris CM tower

Fix the existing normalized Harris CM moduli data over the CM field `F`
and the named hypothesis `CMRepresentabilityStatement` for its small
levels. For a complete ultrametric nontrivially normed extension `K` of `F`,
`cmFieldAnalyticTower` analytifies the actual field pullbacks.
The structure morphisms are locally of finite type by smoothness.
Projectivity gives properness of the original scheme representers, and
separatedness passes to the field pullbacks. The analytification functor on those schemes
then provides the objects and every transporter map in `LocalizedCategory`.
Each analytic level is Hausdorff by separatedness.
The field and schemes are in universe zero. `cmLocalAnalyticTower` uses the
canonical completion with the Library's norm from its discrete valuation.

The middle object of a Hecke span is the original small intersection level.
`cmFieldAnalyticHeckeLeft` maps its forgetting arrow, and
`cmFieldAnalyticHeckeRight` maps the specified right transporter. The two
refinement squares are the original transporter equalities mapped by the
functor. At any level, `cmFieldAnalyticEtaleTopology` and
`cmFieldAnalyticQuasiEtaleTopology` give the actual small analytic étale
and compact-probe quasi-étale topologies.

The construction gives the analytic Shimura-variety side of Harris,
*Galois properties of cohomological automorphic forms on GL(n)* (1999), §4,
printed pp. 308–309, especially (4.3), conditional on the same representability
used for the scheme tower. The local field input can also be a specified
complete extension of the completion. Harris uses extra hypotheses on the
split prime, the unitary datum and the levels for the uniformization. The
analytification of schemes and their maps in this file is functorial for
all the represented small levels over the given field. The uniformization,
analytification of coefficient sheaves, and cohomological comparison are
separate results.
Literature ID `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Berkovich's *Spectral Theory and Analytic Geometry over Non-Archimedean
Fields* (1990), Theorem 3.4.1, proof steps (2)–(3), pp. 63–64, supplies the
affine gluing used by the analytification functor. Theorem 3.4.8(i), p. 67,
gives the Hausdorff conclusion for separated schemes. The literature ID is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`
and the SHA-256 is `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
