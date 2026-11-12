# Naturality of rational scalar extension

`Langlands.GroupScheme.GaloisPointComparison.rationalExtend_map` states that
extension of scalars `G(k) → G(L)` commutes with every group-scheme
homomorphism `f : G ⟶ H`: `rationalExtend (f x) = f_L (rationalExtend x)`,
where `f_L` is the base change of `f`. The fields have the same arbitrary
universe and an arbitrary `Algebra k L`; no affineness or finiteness
hypothesis is imposed.

The proof passes to coefficient-point descriptions through
`baseChangeCoeffEquiv` and `rationalCoeffEquiv`, where it is the naturality
`affinePointsTarget_naturality` of coefficient extension.

The declaration, name and proof are moved unchanged from
[UnramifiedZeroTransport](../../Geometry/Building/UnramifiedZeroTransport.md).
This shared algebraic module is reused by that transport module and by
[KPTorusCharacterFiltration](../../Geometry/Building/KPTorusCharacterFiltration.md).
