# Local dimension induction for Artinian exhaustion

`StalkLocalityStatement` concerns a family of immersions over a noetherian
scheme `S`, indexed by a nonempty directed preorder. The ambient scheme is
locally of finite type and quasi-compact over `S`. If at each point `s` some
family member becomes an isomorphism after pullback to
`Spec O_{S,s}`, then a single member is an isomorphism globally. The
dimension induction takes this statement as an explicit input.

`DimensionBound n` gives exhaustion for the same families when the ambient
map is also locally quasi-finite, the family becomes full after each local
Artinian affine base change, and all base stalks have dimension less than
`n`. Strong induction reduces to a base stalk of dimension `m < n`. Every
local ring of its punctured spectrum has dimension less than `m`, so the
induction hypothesis makes the family full there. Each maximal-ideal-power
quotient is local Artinian, and the testing hypothesis makes the family
full on that thickening. The local geometric exhaustion theorem then makes
one member full over the entire local base.

For an arbitrary noetherian base, each stalk ring has finite dimension. Its
spectrum has a corresponding bound on all stalk dimensions. Applying the
bounded result on each stalk spectrum and invoking stalk locality proves
the general exhaustion assertion.

This is an internal alternative to the maximal-open noetherian induction in
SGA 3, Exposé IX, proof of Lemma 6.2, printed pp.53–54 (retained PDF pp.23–24),
registered as `sga3-expose-ix-gille-polo-2009`, SHA256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
The scheme and index universes are arbitrary.
