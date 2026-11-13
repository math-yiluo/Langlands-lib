# Central characters along an isomorphism of p-adic fields

Worker 5130, Task 5230. Internal derived infrastructure; no external source.

For `f : F ≃ₐ[ℚ_p] E`, `unitsAlgEquiv F E f : Fˣ →* Eˣ` is `f` on units.
`isUnitaryBasisCentralCharacter_unitaryBasisEquiv` and
`isUnitaryCentralCharacter_unitaryLatticeEquiv` show the following: if `ω` is a
central character of a unitary supercuspidal basis class or lattice element over `E`,
then `ω ∘ unitsAlgEquiv F E f` is a central character of its pullback
`unitaryLatticeEquiv F E f` over `F`. For a basis class, the pullback is along
`fieldPullback`, and scalar matrices go to scalar matrices
(`Matrix.GeneralLinearGroup.map_scalar`). `unitaryLatticeEquiv_eq_equivMapDomain`
from `Langlands.VirtualRepresentation.Supercuspidal.FieldTransportLattice`
reduces lattice elements to basis classes.
