# Cyclic relative H2 and the actual field norm quotient

Author: Worker 28.

`Langlands.ClassFieldTheory.Local.cyclicH2NormEquiv K L σ hσ` is an additive
equivalence

```
relativeCohomology K L 2 ≃+ Additive (Langlands.LocalClassField.NormQuotient K L).
```

Its parameters are independently universe-polymorphic fields `K : Type u` and
`L : Type v`, an algebra structure `Algebra K L`, finite dimensionality,
`IsGalois K L`, and an explicit automorphism `σ : Gal(L/K)` satisfying
`hσ : ∀ g, g ∈ Subgroup.zpowers σ`. It requires no supplied cohomological
comparison. Finiteness of the automorphism group comes from finite
dimensionality, and commutativity is derived from the specified generator.
The construction also covers the trivial extension and its trivial group.

The source is exactly the published ordinary group cohomology of
`unitsRepresentation K L`. Its scalar ring remains `IntegerScalars.{v}`,
the explicit `ULift` of the integers used by that representation. Neither
field, its unit group, nor its automorphism group is resized. The target is
exactly the published quotient of `Kˣ` by the image of
`normUnits K L = Units.map (Algebra.norm K)`, where `Algebra.norm` is the
determinant field norm. `Additive` changes group notation only. This final
comparison is an additive equivalence; no linear structure across field
carrier universes is imposed on the target.

## Fixed-unit descent and the field norm

The imported `baseUnitsToInvariants` construction from the `UnitInvariants`
module includes a base-field unit by the algebra map and certifies that every automorphism fixes it. Injectivity follows from
injectivity of the field algebra map. For surjectivity, the value in `L` of an
invariant unit is fixed by all automorphisms. The finite Galois theorem
`IsGalois.mem_range_algebraMap_iff_fixed` gives a preimage in `K`. It is
nonzero because the original element is a unit, and hence defines a unit of
`K`. `invariantUnitsEquiv` reuses the inverse of the existing
`baseUnitsEquivInvariants` additive equivalence. Its forward map selects the
unique descended unit; its inverse is the algebra-map inclusion.

The imported `unitsRepresentation_norm` theorem expands the representation
norm as the sum of all Galois operators. In multiplicative notation this is the product of
conjugates. The proved Mathlib identity
`Algebra.norm_eq_prod_automorphisms` identifies its value with the inclusion
of the determinant norm. Unit extensionality then gives the equality of
actual units. `invariantUnitsEquiv_norm` applies descent and records that the
norm is exactly `normUnits K L`, with no unspecified comparison factor.
This proof works in independent universes and does not invoke Mathlib's
Type-0-only bundled Hilbert-90 norm lemma.

The construction imports `Langlands.Cohomology.Tate.ZeroDefinitions` and
reuses `Langlands.Tate.normToInvariants`, `normImage`, and
`InvariantsModNorm`. It does not redefine those objects or reconstruct the
Tate degree-zero comparison. `invariantNormProjection` descends a fixed unit
and projects it into the existing field norm quotient. Its surjectivity is
proved from descent and surjectivity of the quotient projection. Its kernel
is proved to be exactly `normImage`: membership in the field norm image
provides a unit of `L`, and the preceding norm identity transports that
witness in both directions. The first isomorphism theorem therefore gives
`invariantsModNormEquiv`.

Two private helpers apply the standard additive-group first isomorphism
theorem and provide an identity-on-elements additive equivalence between
the submodule quotient and its underlying additive-subgroup quotient. Their
inverse and additive laws are proved; neither changes a carrier universe.
The public intrinsic certificates are:

- `invariantsModNormEquiv_mk`: the class of an invariant unit maps to the
  class of its descended base-field unit.
- `invariantsModNormEquiv_symm_projection`: the inverse maps the class of
  a base-field unit to the class of its inclusion into `Lˣ`.

## Ordinary H2 comparison and generator dependence

`cyclicH2InvariantsEquiv` invokes the pinned Mathlib construction
`Rep.FiniteCyclicGroup.groupCohomologyIsoEven` at degree two. This compares
ordinary group cohomology, computed by the existing inhomogeneous complex,
with the homology of the cyclic short complex

```
A --N--> A --(ρ(σ) - 1)--> A,  A = unitsRepresentation K L.
```

`ShortComplex.moduleCatHomologyIso` presents that homology as the kernel of
`ρ(σ) - 1` modulo the range of the norm with codomain restricted to that
kernel. Since `σ` generates the group, Mathlib's proved invariant criterion
identifies this kernel with all invariant elements. The private
`cyclicKernelEquivInvariants` is the identity on the underlying elements,
and its range certificate proves that the restricted norm image becomes
exactly the imported `Langlands.Tate.normImage`. The submodule quotient
equivalence then gives `cyclicH2InvariantsEquiv`.

The final `cyclicH2NormEquiv` composes its underlying additive equivalence
with `invariantsModNormEquiv`. Its forward map first uses the cyclic
resolution to obtain a fixed-unit class, then descends that class to the
field norm quotient. Its inverse includes a representative base-field unit
into the invariant-unit quotient, identifies it with a cyclic-complex
homology class, and applies the inverse cyclic-resolution comparison.
Both composites are identities because each constituent is a proved
isomorphism or equivalence. Well-definedness follows from the explicit norm
image transport and kernel certificates above.

The choice of generator enters through Mathlib's cyclic-resolution
comparison. The field-specific descent and quotient equivalence do not
use a generator. We make no assertion that the final equivalence is
independent of `σ`, and do not identify its inverse with the separately
published `cyclicClass` carry cocycle. Such a normalization theorem is outside
this construction. No local reciprocity or local invariant existence theorem
is claimed here; no topology, completeness, or valuation is needed.

## Original source and implementation provenance

Jean-Pierre Serre, *Local Fields*, English translation by Marvin Jay
Greenberg, Springer GTM 67 (1979), Chapter VIII, section 4, Proposition 6 and
its corollary, printed pages 132–133 (PDF pages 138–139). Serre uses the
cyclic complex with alternating operators `σ - 1` and the group norm and
identifies positive even cohomology with invariants modulo norms. The
remark on page 133 explicitly records dependence on the chosen generator.
Chapter XIII, section 2, corollary to Proposition 5, printed page 192 (PDF
page 197), applies this computation to relative multiplicative field
cohomology, identifying cyclic relative H2 with `Kˣ/N(Lˣ)`.

Source ID: `serre-1979-local-fields`. Retained file:
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`. SHA256:
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 28 read these original passages. The implementation is the
field-specific specialization of this cyclic computation. Its kernel,
descent, quotient, and transport certificates are intrinsic formalization
work, proved from the cited Library and Mathlib interfaces.

The pinned Mathlib revision is
`5ed2965256430c3649e86755f9576b54eca72435`, with Lean 4.34.0. Relevant source
files are `RepresentationTheory/Homological/GroupCohomology/FiniteCyclic`,
`RepresentationTheory/Homological/FiniteCyclic`,
`Algebra/Homology/ShortComplex/ModuleCat`, `RepresentationTheory/Invariants`,
`FieldTheory/Galois/Basic`, and `RingTheory/Norm/Basic`. The elementary
product proof in `GroupCohomology/Hilbert90` informed the lifted norm proof;
its restricted-universe theorem is not an input to this construction.
