# Vanishing of actual continuous local inertia H2

Authors: Worker 37 and Worker 10. Worker 10's private draft supplied the
finite-stage helper `absoluteH2_of_finiteRelativeH2`; Worker 37 implemented
the fixed-field transport and final assembly.

`Langlands.ClassFieldTheory.Local.inertiaH2Vanishing` proves exactly
`Langlands.ClassFieldTheory.Local.InertiaH2Vanishing.{u}`. For every prime
`p` and `F : PadicField.{u} p`, continuous degree-two cohomology of the
actual canonical inertia subgroup with its restricted discrete
algebraic-closure unit action is a subsingleton. The common universe `u`
is arbitrary. The coefficient scalar ring remains `IntegerScalars.{u}`,
and the inertia group retains its inherited subtype topology. The theorem
has no additional hypotheses.

The final proof uses the published arithmetic theorem
`inertiaFixedFieldNormSurjectivity` from
[InertiaFixedFieldNormProof](InertiaFixedFieldNormProof.md), authored by
Worker 60, and the published finite-group theorem
`finiteNormH2Vanishing.{u,v}` from
[FiniteNormH2Proof](FiniteNormH2Proof.md), authored by Worker 68. These are
used through their published declarations.

Put `U` equal to the literal fixed field of
`F.absoluteInertia F.canonicalTopologicalData`. For each finite Galois
stage `L/U` in `AlgebraicClosure U` and each intermediate field `E`,
the extension `E/U` is finite and `L/E` is finite Galois. The arithmetic
theorem gives surjectivity of the determinant norm on all field units
from `L` to `E`, using the original intermediate-field scalar maps.
Thus `finiteNormH2Vanishing.{u,u}` proves vanishing of every relative H2
stage. Specializing its independent universe parameters to the common
universe supplies exactly the instance needed here.

The private helper `absoluteH2_of_finiteRelativeH2` then passes to absolute
continuous H2. Each open normal subgroup of the absolute Galois group
corresponds, by Mathlib's infinite Galois correspondence, to a finite
Galois fixed field. The published `fixedFieldCohomologyIso` identifies
the quotient's fixed-unit cohomology with that relative field cohomology.
All these groups are subsingletons. The colimit universal property
therefore makes the identity on the finite-quotient cohomology colimit
zero, so that colimit is a zero object. The published
`finiteQuotientComparisonLinearEquiv` transports this vanishing to the
actual absolute continuous homogeneous cochain model.

The private helper `inertiaH2Vanishing_of_fixedField` transports that
vanishing to the required inertia action. Published closedness and
normality of the actual canonical inertia subgroup make its fixed field
normal over `F.Carrier`. A chosen `F.Carrier`-linear embedding of
algebraic closures supplies the scalar tower required by the published
`closureSubgroupEquiv` and `closureSubgroupCoefficientsIso` from
[ClosureUnitTransport](ClosureUnitTransport.md). They identify the
absolute Galois group and discrete unit action of `U` with the fixing
subgroup and the restricted unit action in the original closure.
The infinite Galois correspondence identifies this fixing subgroup
with the original closed inertia subgroup. The published continuous
cohomology transport isomorphism then gives exactly the conclusion of
`InertiaH2Vanishing`.

This is a derived assembly of those field, topology, coefficient and
cohomology comparisons. Its provenance is Serre, *Local Fields*,
Greenberg English translation, GTM 67 (1979), registered
`serre-1979-local-fields`, Chapter V, Section 4, Proposition 7
(printed pages 89–90 / PDF pages 96–97), and Chapter X, Section 7,
Proposition 11, its proof and example b (printed pages 161–162 /
PDF pages 167–168). The registered source is retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The implemented finite norm criterion uses the published finite-group
proof, and the passage to the actual continuous model uses the stated
finite-quotient comparison and closure transport. All arithmetic and
comparison inputs are proved dependencies; none remains a premise of
the theorem.
