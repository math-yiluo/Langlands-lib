# The quotient map to the bundled opposite Jacquet module

`Langlands.PadicField.TopologicalData.oppositeJacquetMk T C A` is the actual
linear quotient map `Jacquet.mk A.ρ (C.oppositeUnipotentSubgroup F.Carrier)`
with target the carrier of `CuspidalJacquetMultiplicity.oppositeJacquet T C A`.
Here `T` is the supplied topological data for a p-adic field, `C` a block shape,
and `A` a complex representation of the corresponding general linear group.
The field and representation carrier have independent universes.

This definition is extracted unchanged, with its published name, from
[MaximalConeLifting](../Classification/MaximalConeLifting.md). That module keeps
its surjectivity, radical-invariance, and normalized-action lemmas. The tensor
comparison in [RefinedOppositeJacquetTensor](RefinedOppositeJacquetTensor.md)
reuses this quotient map without importing the exponent-lifting development.
No smoothness, admissibility or irreducibility assumption is added.
