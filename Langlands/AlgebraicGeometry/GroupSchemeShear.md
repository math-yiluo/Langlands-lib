# The shear automorphism of the square of a group scheme

Module `Langlands.AlgebraicGeometry.GroupSchemeShear`.

## Maps of fibre products

For schemes `Y, Z` over `S`, `Y', Z'` over `T`, maps `y : Y' ⟶ Y`, `z : Z' ⟶ Z` over a base map
`t : T ⟶ S`, `productMap y z t hy hz : (Y' ⊗ Z').left ⟶ (Y ⊗ Z).left` is the induced map of fibre
products (module `ElementaryReductionProducts`). This module adds its projections
(`productMap_fst`, `productMap_snd`, `productMap_pullback_fst`, `productMap_pullback_snd`), its
structure map (`productMap_hom`), extensionality (`productMap_ext`), composition
(`productMap_comp`) and identity (`productMap_id`). The instances `isSeparated_tensor_hom` and
`smooth_tensor_hom` record that the product in schemes over `S` of two separated (smooth) schemes
is separated (smooth).

## The shear

For a group object `G` of a cartesian monoidal category, `shear G : G ⊗ G ≅ G ⊗ G` is the
isomorphism `(x, y) ↦ (x * y, y)`, with inverse `(x, y) ↦ (x / y, y)`. `shear_hom_fst`,
`shear_hom_snd`, `shear_inv_fst` and `shear_inv_snd` compute its components, and `fst_mul_snd`
identifies `fst * snd` with the multiplication `μ`.

## Multiplicative maps

For monoid objects `G` over `T` and `H` over `S` in schemes, a map `f : G.left ⟶ H.left` over
`b : T ⟶ S` is multiplicative (`IsMulMap b f hf`) if `μ_G ≫ f = (f × f) ≫ μ_H`, with `f × f` the
`productMap`. This holds for identities (`isMulMap_id`), is stable under composition
(`IsMulMap.comp`), and holds for the first projection of a base change
`(Over.pullback b).mapGrp.obj H ⟶ H` (`isMulMap_pullback_fst`, from the multiplicativity of
`GroupScheme.baseChangePointsEquiv`). A multiplicative map between group objects commutes with
the shears (`IsMulMap.shear_hom`, `IsMulMap.shear_inv`).

## Provenance

The shear is the automorphism `(x, y) ↦ (x + y, y)` of `A × A` used in Kai-Wen Lan,
*Arithmetic compactifications of PEL-type Shimura varieties*, Harvard thesis revised 14 March
2021, proof of Proposition 2.2.4.1 (printed pp. 152–154, PDF pp. 180–182). The two formulas for
the shear and its inverse are verified by the product projections and the group laws.
