# Proof of coefficient naturality

This module imports the target statement
`Langlands.Continuous.CoefficientComparisonLaws` and its dependencies
unchanged. The target was published in Library commit
`7db0c477a21f8471b1e5cff5f20d8ecb3dd2285b`; its pair is unchanged in
the Library base `b164b3aa3952e5f6000986e04be27b200c582796` of this proof.

`Langlands.Continuous.coefficientComparisonLaws` proves exactly the
imported `Langlands.Continuous.CoefficientComparisonLaws` in arbitrary
common universe `u`.

`finiteCochainCoefficient_comp_stage` cancels the injective canonical
continuous-to-ordinary cochain map for the target coefficients. The
proved naturality of that comparison and its finite-stage formula reduce
the square to ordinary cochain functoriality. The two composed group
homomorphisms agree, and the coefficient maps are definitionally the
same underlying morphism on fixed vectors.

`finiteCohomologyCoefficient_comp_stage` applies homology to this
cochain equality. Naturality of the short-complex homology isomorphism
for the topology-forgetful functor identifies the resulting map with
Mathlib's actual continuous coefficient map in each natural degree.

For `finiteQuotientComparison_coefficient_naturality`, colimit
extensionality reduces the assertion to each finite stage.
`Limits.ι_colimMap` computes the coefficient map after a colimit
inclusion. The defining stage formula for the comparison and the
preceding homology equality then give the required square.
The final theorem collects these three assertions without additional
hypotheses. It quantifies over every commutative ring equipped with a topology, every topological
group, every pair of discrete jointly continuous coefficient modules,
and every continuous equivariant coefficient morphism, in the common
universe `u`. The coefficient map on ordinary representations is exactly
`Rep.ofHom f.hom.toIntertwiningMap`; the continuous map is
`ContinuousCohomology.map` for the identity group homomorphism and `f`.
No compactness or invertibility of the colimit comparison is needed.

The mathematical provenance is Serre, *Local Fields* (1979), VII §5
and X §3. More precisely, VII §5, printed pp.115–117 / PDF pp.121–123,
supplies compatible coefficient and group maps and inflation; X §3,
printed p.154 / PDF p.160, supplies the inflation-indexed direct limit.
The argument above for the named maps in Mathlib's nested continuous
cochain model is derived implementation work and is the implemented
proof. Literature ID `serre-1979-local-fields`; source SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`;
retained file `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.

Pinned environment: Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
