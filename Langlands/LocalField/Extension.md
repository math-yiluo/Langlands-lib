# Supplied and spectral local-field data over an arbitrary base

Worker 845 generalizes the existing p-adic realization mechanism for Task 7403.
`Langlands.LocalField.TopologicalData K₀ L` records a local-field realization of
an extension of fields, with a specified base valuative relation and topology.
Its five fields are `topology`, `valuativeRel`, `valuativeExtension`,
`moduleTopology`, and `localField`. The valuation prolongs the base comparison
along the specified algebra map; the topology is the base module topology.
`TopologicalData.Integers`, `.ResidueField` and `.residue` use exactly the
supplied valuation ring, its residue field and its quotient map.

The data package itself requires neither finite degree nor a characteristic.
The spectral constructors take a complete, nontrivially normed ultrametric
base `K₀` and a finite extension `L`. `canonicalNorm`, `canonicalNormedField`,
`canonicalNormedAlgebra` and `canonicalTopology` are Mathlib's spectral norm,
its field/algebra structures and the base module topology. `canonicalValuation`
uses `Langlands.LocalGalois.spectralValuation` for its nonnegative-real norm valuation. `canonicalValuativeRel` is the relation
induced by that valuation. These are explicit constructions, not global instances.

`canonicalTopologicalData K₀ L hbase` additionally assumes local compactness
of the base and a specified valuative relation whose comparisons satisfy
`hbase : ∀ a b, ‖a‖ ≤ ‖b‖ ↔ a ≤ᵥ b`. The proof input ties the chosen norm
to the existing base relation; it does not supply a mathematical existence
claim. The constructor proves all extension certificates. Spectral extension
of the norm proves valuative compatibility using `hbase`. The norm-valued
neighborhood basis proves the valuative topology. `FiniteDimensional.proper`
proves properness, hence local compactness, and nontriviality of the norm
valuation proves that of the relation. Finite-dimensional normed-space theory
supplies the module-topology certificate.

This extends the implementation already used in `PadicField.canonicalTopologicalData`.
The existing `LocalField.FiniteExtension` module is also spectral, but chooses
`LocalGalois.localNormedField K` on its local base. The present base-parameterized
constructor permits both that choice and the original norm on `Padic p`,
which is necessary to retain the original p-adic definitions by unfolding.
No comparison between two ramification theories is introduced.

## Source and in-place specialization

Serre, *Local Fields* (1979), Chapter II, §1 Proposition 1, p.27, and §2
Proposition 3 and Corollaries 2–3, pp.28–29, give the finite-extension topology
and prolongation conventions. Source `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
These pages were read in the original. The registered 2019 author corrections,
`serre-book-corrections-2019`, PDF pp.2–3, were checked; they do not change
these passages. The structure and spectral implementation are internal packaging
of Mathlib constructions, not structures asserted verbatim by Serre.

| General declaration in `Langlands.LocalField` | Existing p-adic specialization |
| --- | --- |
| `TopologicalData (Padic p) F.Carrier` | `F.TopologicalData`, via `.toLocalData` and `.ofLocalData` copying all five fields |
| `canonicalNorm (Padic p) F.Carrier` | `F.canonicalNorm` |
| `canonicalNormedField (Padic p) F.Carrier` | `F.canonicalNormedField` |
| `canonicalNormedAlgebra (Padic p) F.Carrier` | `F.canonicalNormedAlgebra` |
| `canonicalTopology (Padic p) F.Carrier` | `F.canonicalTopology` |
| `canonicalValuation (Padic p) F.Carrier` | `F.canonicalValuation` |
| `canonicalValuativeRel (Padic p) F.Carrier` | `F.canonicalValuativeRel` |
| `canonicalTopologicalData (Padic p) F.Carrier hbase` | `F.canonicalTopologicalData`, after `.ofLocalData` |
| `T.toLocalData.Integers`, `.ResidueField`, `.residue` | `T.Integers`, `.ResidueField`, `.residue` |

All rows agree definitionally after unfolding the field-preserving wrappers.
The existing `PadicField.canonicalNorm` retains its direct `spectralNorm` body
so that published proof scripts that explicitly unfold it continue to work.
The original `PadicField` and `PadicField.TopologicalData` structures, their
constructors and all original field names and types remain intact. The new
conversions do not install instances or change the integer ring. The p-adic
`hbase` follows from `Padic.norm_lt_norm_iff_mulValuation_lt`; proof irrelevance
identifies the compatibility fields with their former proofs.

There was no implicit characteristic-zero use in these finite spectral
constructions: neither the general base nor its finite extension needs to be
perfect or separable. In the local-field application the base norm is
`LocalGalois.localNormedField K`, whose completeness, ultrametricity and comparison
lemmas are already published for every `IsNonarchimedeanLocalField K`.
The replacement of an algebraic closure by a separable closure belongs to the
absolute-filtration unit, not this foundational data package.

Development check `6eaa79d3-715c-4758-ad0b-168453aa7af5` compiled the unchanged
canonical and normalization proof consumers. A private diagnostic also checked
by `rfl` that the original canonical valuation, valuative relation and full
topological-data constructor are the new ones, and that both integer-ring
presentations are identical. Inspection of the general constructor reports only
`propext`, `Classical.choice`, and `Quot.sound`. This is development evidence;
independent review and publication remain separate.

A further consumer check `df82c366-330b-4a3c-baa6-13f003161985` compiled
`CanonicalProof`, `Normalization.Proof` and `Weil.Local.ExtensionResidue` with
zero diagnostics after retaining the original outer norm expression.
