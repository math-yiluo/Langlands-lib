# Canonical topological realization of a p-adic field

`Langlands.PadicField.canonicalTopologicalData F` constructs
`F.TopologicalData` from every algebraic `F : PadicField p`. The prime `p`
is arbitrary under `[Fact p.Prime]`, and `F.Carrier` may live in any universe
`u`. The construction needs only the field, algebra, and finite-dimensional
structures already contained in `F`.

This pair contains three definitions:

- `canonicalValuation F : Valuation F.Carrier NNReal` is the valuation whose
  value is the nonnegative spectral norm.
- `canonicalValuativeRel F` compares these valuation values.
- `canonicalTopologicalData F` equips the carrier with the spectral norm
  topology, this relation, and every certificate required by the accepted
  `TopologicalData` interface.

The constructor supplies the certificates from Mathlib and explicit proofs;
it takes no topological realization or existence assertion as an input.
There is no restriction on the extension degree, normality, Galois group,
or ramification.

## Construction and instance selection

First install the accepted explicit `F.canonicalNormedField` and
`F.canonicalNormedAlgebra` structures. Mathlib's
`isNonarchimedean_spectralNorm` makes their distance ultrametric. The
definition `NormedField.valuation` then gives an `NNReal`-valued valuation,
and `ValuativeRel.ofValuation` gives its relation.

For the topology certificate, `NormedField.toValued` describes the
neighborhoods of zero using precisely this valuation while retaining the
norm's uniform space. `IsValuativeTopology.of_mem_nhds_zero_iff_vle`
converts that description to the required valuative-topology certificate.
This establishes compatibility with the selected topology.

`FiniteDimensional.proper` gives properness over the locally compact base
`Padic p`, hence local compactness. The norm valuation has rank one because
the selected norm is nontrivial. Its nontriviality transfers to the
valuative relation through `ValuativeRel.isNontrivial_iff_isNontrivial`.
These three properties assemble `IsNonarchimedeanLocalField`.
`isModuleTopologyOfFiniteDimensional` supplies the module-topology
certificate. These arguments use the arbitrary finite extension; they do
not use a normal-extension-only spectral norm result.

Finally, `spectralNorm_extends` identifies the norm on the image of
`Padic p`. The existing theorem
`Padic.norm_lt_norm_iff_mulValuation_lt`, applied through negated strict
inequalities, identifies non-strict comparisons. This proves both directions
of `ValuativeExtension.vle_iff_vle` for the specified algebra map and the
existing p-adic valuative relation.

No global norm, topology, or valuative-relation instance is installed by
this module. A caller can use the topological interface as follows:

```lean
let T := F.canonicalTopologicalData
letI := T.topology
letI := T.valuativeRel
letI := T.valuativeExtension
letI := T.moduleTopology
letI := T.localField
```

For calculations that also use a norm or uniform space, install
`F.canonicalNormedField` and `F.canonicalNormedAlgebra` first, then the
canonical realization's valuative relation and certificates. The realization's
topology is the one carried by that normed field.

With `open scoped ValuativeRel`, Mathlib then provides the compact integer
ring `𝒪[F.Carrier]`, its `IsDiscreteValuationRing` instance, the finite
residue field `𝓀[F.Carrier]`, and `ValuativeRel.IsDiscrete F.Carrier`.
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier` supplies
the ordered value-group isomorphism with the integers in multiplicative
notation, with zero adjoined. Discreteness concerns the valuation's value
group; the numerical codomain `NNReal` itself is not a discrete group.
Completeness for the spectral uniformity is available through
`spectralNorm.completeSpace` or `FiniteDimensional.complete`.
The separate compatibility target records these uses and the
explicit topology and norm comparisons.

## Normalization and original sources

The numerical norm extends the usual p-adic norm. In particular, the
image of the integer `p` has norm `(p : Real)⁻¹`. Serre's normalized
local-field absolute value instead assigns `q⁻¹` to a uniformizer, where
`q` is the residue-field cardinality. The construction here selects the
base-extending norm. Ramification indices and the conversion to the
residue-cardinality normalization belong to the separate arithmetic
development.

The mathematical domain is Henniart's arbitrary finite extension of `Q_p`.
The topology and prolongation conventions follow Serre's finite-extension
theory. The packaging and the route through the spectral norm and Mathlib
typeclasses are internal implementation choices.

- Guy Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
  sur un corps p-adique*, Inventiones mathematicae 139 (2000), Section 1.1,
  page 439, first two sentences (PDF page 1).
  Source ID `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
  Actual file:
  `C:/Central-Library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`.
- Jean-Pierre Serre, *Local Fields*, English translation by Marvin Jay
  Greenberg, Graduate Texts in Mathematics 67, Springer, 1979.
  Chapter II, Section 1, pages 26-28, especially Proposition 1, its `Q_p`
  example, and the normalization preceding Proposition 2; Section 2,
  Proposition 3 and Corollary 2, pages 28-29, and the absolute-value
  discussion on page 30 (PDF pages 34-38).
  Source ID `serre-1979-local-fields`, SHA256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
  Actual file: `C:/Central-Library/Serre--Local Fields--1979.pdf`.

Worker 26 read these original passages and verified their file hashes.
Serre identifies the finite-extension topology with the finite-dimensional
product topology and proves completeness and uniqueness of prolongation.
The Lean constructor reuses Mathlib's proved results for these ingredients.
It does not formalize the identification with an integral closure, the
ramification degree formula, or a norm formula involving a field norm.

## Exact dependencies and validation

The sole project import is `Langlands.LocalField.Definitions`, accepted
definition artifact `ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0`, version 1.
Its publication commit is `1fe07fd211e579cc430734fd96ce959aadb7663d`,
with independent receipt `203bba66-269f-46f4-984c-71531a4963c2` and
effective snapshot
`7dd12688f9e4cc615cd460940f0a82295c62729f3d59bb86304e3627c6831512`.
The exact accepted Lean and Markdown hashes are respectively
`8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517`
and `6cfb939cf42a71a81fa648b77bd4bab1076bffe0d62519181f7dc7db742124bf`.
They were checked against the local files and current Library membership.

Environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, pins
Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and Mathlib
at `5ed2965256430c3649e86755f9576b54eca72435`. The additional direct imports
are `Mathlib.Analysis.Normed.Module.FiniteDimension` and
`Mathlib.Topology.Algebra.Valued.NormedValued`. The valuative-relation
constructors are in `RingTheory/Valuation/ValuativeRel/Basic.lean` and
`Topology/Algebra/ValuativeRel/ValuativeTopology.lean`; the downstream
instances are in `NumberTheory/LocalField/Basic.lean`.

Worker 26 authored this pair. Native compilation succeeds without errors
or warnings. Axiom inspection of the constructor reports only `propext`,
`Classical.choice`, and `Quot.sound`. The constructor fields contain complete proofs and introduce
no project axiom or placeholder. Compilation is development evidence;
independent semantic review and publication establish acceptance of this
definition contribution. The explicit compatibility results require a
separately accepted proposition target and independently checked proof.
