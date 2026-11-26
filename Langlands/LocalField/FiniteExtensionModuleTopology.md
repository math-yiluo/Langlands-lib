# Spectral and module topology on a finite extension

Let `F` be a nonarchimedean local field and `E/F` a finite field extension.
The Library module `Langlands.LocalField.FiniteExtension` already equips
this very field `E` with its spectral norm, spectral valuative relation and
nonarchimedean local-field structure. This internal module compares the
topologies, for consumers whose ambient topology on `E` is supplied as a
module topology rather than introduced by the spectral norm.

- `spectralTopology_eq_moduleTopology` proves that the topology of
  `FiniteExtension.normedField F E` equals `moduleTopology F E`. Give `F`
  its Library normed-field structure (whose topology is the original one),
  give `E` the spectral norm and compatible normed-algebra structure, and
  choose a finite `F`-basis. The coordinate map of this basis is a continuous
  linear equivalence with a finite product of copies of `F`. Such a product
  has the module topology, so the inverse coordinate map transports it to `E`
  by Mathlib's `IsModuleTopology.iso`.
- `spectralTopology_eq` gives the same equality with any originally supplied
  topology on `E` satisfying `IsModuleTopology F E`, by uniqueness of the
  module topology.
- `isLocalField_of_isModuleTopology` supplies `IsNonarchimedeanLocalField E`
  for `FiniteExtension.valuativeRel F E` and the supplied topology, by
  transporting the existing `FiniteExtension.isLocalField` along this
  equality. In particular, a consumer can use `LocalFieldData.ofInstances E`
  without replacing its topological field.

The assertions are derived compatibility lemmas, not new constructions of
valuations or local fields. There is no cyclicity or characteristic-zero
hypothesis. The intended application is to the ambient extension field in
Henniart–Lemaire (2011), II.5.1, in the proof of the Library's twisted
pseudo-coefficient existence statement.
