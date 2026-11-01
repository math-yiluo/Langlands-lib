# Reduction of CM base admissibility to actual dual geometry

Worker 147. This is an internal derivation from the imported Library
constructions. It characterizes the remaining admissibility obligation
on an actual locally Noetherian CM base; it does not construct a moduli
scheme or prove division-case CM representability.

`CMBaseDualGeometry S` says that every abelian scheme over the specified
scheme `S` has an actual universal geometric Picard-zero parameter and
that this same chosen parameter is smooth, proper and geometrically
connected. Its definition uses the existing `HasDualScheme` and
`DualSchemeGeometry`, without changing the universal property or its
test category.

`dualEvaluationDataOfGeometry` constructs the existing constrained
`DualEvaluationData` from such a fixed dual and its geometry.
`LineBundle.exists_tensorObj_iso_structureSheaf` supplies the tensor
inverse of the actual Poincare line bundle and its evaluation isomorphism.
`relativeDualSchemeMapAdditivity` supplies additivity for the actual dual
endomorphisms. The converse extracts `hasDual` and `geometry`. Thus
`nonempty_dualEvaluationData_iff` identifies the constrained data's
nonemptiness with dual existence and geometry. It asserts no
unconditional dual existence.

The other admissibility fields are derived as follows.

- The structure morphism to the characteristic-zero field induces a ring
  map to global sections. Mapping the unit represented by a positive
  natural number through that map proves `cmBaseTorsionUnit`.
- `muFiniteEtale` applies to this positive invertible index and gives
  finiteness and etaleness of the actual roots-of-unity group scheme.
- `lieBaseChangeNaturalityStatements` gives the required actual
  all-homomorphism Lie naturality.
- `positivePairAdditivity` applies the published dual-map additivity
  theorem to each ordered pair of actual positive-auxiliary polarized
  actions, with their own dual parameters.
- Mathlib proves quasi-separatedness of every locally Noetherian
  scheme. The existing connected-component construction supplies
  connectedness and local Noetherianity of each actual component scheme.

Consequently `admissibleCMBase_iff_dualGeometry` characterizes the exact
existing `AdmissibleCMBase` on a connected locally Noetherian scheme over
the CM field. `componentwiseAdmissibleCMBase_iff_dualGeometry` gives the
same characterization on every actual connected open component. The
component scheme and its structural morphism are the existing
`componentCMOver`; there is no change of test category.

`componentwiseAdmissibleCMBase_of_relativeDual` supplies these remaining
fields from the two explicitly named proposition hypotheses
`RelativeDualSchemeExistenceStatement` and
`RelativeDualSchemeGeometryStatement`. The smooth specialization derives
local Noetherianity from local finite type over the number field before
applying that bridge. These hypotheses are substantive unproved
prerequisites in this module. They are not additional hypotheses for a
purported proof of `DivisionCMRepresentabilityStatement`, and the
conditional bridge does not discharge that target.

The provenance is entirely internal: the implemented argument assembles
the imported Lie naturality, roots-of-unity, inverse line-bundle and
actual dual-map additivity results. It introduces no new source
transcription, axioms, representing scheme or moduli comparison.
The two relative dual assertions remain in their existing independent
workflows; this file proves neither of them and does not resume their
ordinary Picard or field-existence dependencies. The exact normalized CM
presheaf and all imported Lean/Markdown pairs remain unchanged.
