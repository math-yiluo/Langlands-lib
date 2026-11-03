# Conditional Iwasawa assembly on actual adelic points

Authors: Worker 399 and Worker 1430.

This derived module specializes the published coordinate patching and assembly
lemmas to the actual adelic point group. It retains local Iwasawa existence at
every place and a supplied family satisfying
`IntegralIwasawaFamily.IsIntegralIwasawaFamily` as explicit hypotheses.
It does not prove `AdelicGroupPoints.ParabolicIwasawaStatement`.

`AdelicGroupPoints.extendFinite` extends a family of finite-place subgroups to
`Place F` by taking the full subgroup at each archimedean place. This extension
introduces no compactness claim at those places.

`exists_parabolicIwasawaCompact_of_local_integral` assumes that the underlying
schemes of both group schemes are affine. At every place it assumes the existence
of a compact subgroup maximal among all compact subgroups and satisfying the
literal parabolic-image-left covering equality. It also takes a finite-place
family satisfying the three published integral-family conditions: almost
everywhere local compactness, maximality and covering; absorption of each actual
finite-adelic point; and uniform almost-everywhere integrality of every regular
function on each member. No connected reductivity or parabolicity is needed for
this conditional assembly step.

The conclusion is existence of a subgroup of the existing
`AdelicGroupPoints F G` satisfying the existing
`IsParabolicIwasawaCompact F G P p`. Its compactness uses the existing
regular-function evaluation topology on actual scheme points over the adele
ring. Maximality is among all compact subgroups. The covering uses the actual
continuous homomorphism `AdelicGroupPoints.map F P G p`, with its image on the
left and the compact factor on the right.

The proof extends the finite-place family and regroups its local conditions
into `CoordinateCompactPatching.IsLocalIwasawaCompact`. Since there are finitely
many archimedean places, the extended family is good at almost every place.
The coordinate patching theorem replaces its finitely many bad members using
the assumed local existence. Uniform integrality survives these finite changes
and supplies a continuous full-product lift through the published
`IsUniformlyIntegral.compactProductLift`.

The other inputs to coordinate assembly are now proved adapters rather than
additional hypotheses: `ext_atPlace` separates actual adelic points;
`atPlace` is continuous; `atPlace_map` gives naturality for the actual parabolic
map; `eventually_atPlace_mem_of_finite` transfers the absorption condition; and
`exists_atPlace_eq_of_eventually_one` lifts the finite-support source family.
The coordinate assembly theorem then yields compactness, unrestricted
maximality and exact coverage.

The provenance is internal and derived from the published
`AdelicGroupLocalPoints`, `CoordinateCompactPatching`, and
`IntegralIwasawaFamilyStatement` interfaces. Worker 1430 designed the actual
coordinate specialization. Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), §2.3, Proposition 2.3.1, printed pp.56–57, and §2.7,
Theorem 2.7.1, printed p.71, motivate this assembly. The separate local and
integral inputs are discussed in Appendix B, Theorem B.2.5 and Proposition B.3.1,
printed pp.543–547, and the local results in B.4, printed pp.547–548.
Registered source: `getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The October 2026 errata has no correction to these passages.

To obtain the unconditional adelic target still requires proofs of local
existence at all places, the integral-family existence statement, and
affineness from the original algebraic hypotheses. None is discharged by the
conditional theorem.
