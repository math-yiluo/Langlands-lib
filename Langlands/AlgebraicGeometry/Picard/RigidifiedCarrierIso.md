# Rigidified line bundles with isomorphic underlying bundles

Module `Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso` is a helper
module for the proof of
`Langlands.AbelianScheme.FieldDualSchemeMapAdditivityStatement`. It shows that
two rigidified line bundles are isomorphic as soon as their underlying module
sheaves are, provided the rigidification section `ε : S ⟶ X` has a retraction
`p : X ⟶ S` (`ε ≫ p = 𝟙 S`). The consumer uses this to obtain an isomorphism of rigidified bundles from
an isomorphism of ordinary line bundles. The construction may change the
supplied underlying isomorphism; it does not assert that this isomorphism
already respects the rigidifications.

All declarations are in the namespace
`Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle`, and take an explicit parameter
`preservation : pullbackTensorComparisonIsIsoStatement.{u}` where tensor
products occur. The base and total schemes are arbitrary in universe `u`.
The split section is the only geometric hypothesis; no smoothness,
properness, field or reducedness hypothesis is used.

## Declarations

* `twistedTrivial ε c` is the trivial line bundle on `X` with rigidification
  `O_S ≅ ε^* O_X` given by
  `c ≪≫ (pullbackUnitIso ε).symm`, for an automorphism `c : O_S ≅ O_S`.
  Its inverse is `(pullbackUnitIso ε) ≪≫ c.symm`.
  It is built with the Library constructor `ofLineBundle`.
* `unitor_tensorMap_unitor` is a computation in the module category of `S`:
  for maps `b : O_S ⟶ P` and `c : O_S ⟶ O_S`, the composite of the inverse
  left unitor, `tensorMap b c` and the right unitor of `P` is `c ≫ b`. The
  proof splits `tensorMap b c` into `tensorMap 1 c ≫ tensorMap b 1`, uses
  naturality of both unitors, and the Library identity
  `tensorUnitors_equal` (left and right unitors of `O_S ⊗ O_S` agree).
* `tensorTwistedTrivial_compatibility L c` says that, after the right unitor
  `L ⊗ O_X ≅ L`, the rigidification of `L ⊗ twistedTrivial ε c` is
  `c` followed by the rigidification of `L`. It unfolds the Library
  description `RigidifiedModule.tensorObj_rigidification_comp` of the tensor
  rigidification, uses the published unit coherence
  `pullbackTensorUnitCoherence` (from
  `Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs`), and finishes
  with `unitor_tensorMap_unitor`.
* `isoOfCarrierIso preservation p hp e`: given rigidified line bundles `L`,
  `M` along `ε` and an isomorphism `e` of underlying module sheaves, it
  produces an isomorphism `L ≅ M` of rigidified line bundles. Let
  `c : O_S ≅ O_S` be the discrepancy of `e` with the two rigidifications.
  Then `e` followed by the inverse right unitor is a rigidified isomorphism
  `L ≅ M ⊗ twistedTrivial ε c` (by `tensorTwistedTrivial_compatibility`).
  Because `ε` has the retraction `p`, the Library lemma
  `trivialIsoOfCarrierIso` (from `RigidificationAdjustment`) makes
  `twistedTrivial ε c` isomorphic to the trivial rigidified bundle, and the
  Library right unit isomorphism `tensorRightUnitIso` removes it.
* `nonempty_iso_of_forget_iso preservation p hp e` is the same statement for
  an isomorphism `e` of the images under the forgetful functor
  `RigidifiedLineBundle.forget ε`, in `Nonempty` form.

## Provenance

This is an internal formalization lemma. Mathematically it is the standard
fact that the rigidification of a line bundle along a section with a
retraction can be changed by any unit of the base, by multiplying with the
pullback of that unit.

The Lean construction and elementary verification lemmas were drafted by
Worker 270 for the shared field-additivity proof. Worker 417 extracted the
pair, checked it against its published imports and clarified this description.
This module supplies only these categorical constructions; the geometric
theorem of the square and additivity of the actual dual maps remain separate
obligations.
