# Closed subgroups of the ideles containing almost all local multiplicative groups

Author: Worker 5137. The density argument is adapted from Worker 116's unreviewed draft of
the proof of Hecke-character rigidity (shared draft of task
`34b81620-20d7-4059-9b08-6bedd1c1c029`), where it is applied to the kernel of a quotient of
two characters. Here it is stated for an arbitrary closed subgroup.

This helper module belongs to the proof of
`Langlands.ClassField.Global.RelativeWeilGroup.AssociatedCentralCharacterStatement` (Task 5210).

## Main result

`Langlands.Global.IdeleDensity.eq_top_of_isClosed`: let `K` be a number field, `H` a
subgroup of the idele group `Ideles K`, and `S` a finite set of finite places. Suppose that
`H` is closed, that `diagonalUnits K a ∈ H` for every `a : Kˣ` (principal ideles), and that
`finiteIdeleInclusion K v a ∈ H` for every finite place `v ∉ S` and every
`a : (FiniteCompletion K v)ˣ`. Then `H = ⊤`.

This is the standard consequence of weak approximation: modulo the local groups outside
`S`, an idele is determined by its archimedean and `S`-adic components, and `Kˣ` is dense in
the product of these local groups.

## Auxiliary declarations (namespace `Langlands.Global.IdeleDensity`)

- `coord v` and `infPart`: the coordinate at a finite place `v` and the archimedean part of
  an idele, as monoid homomorphisms. `idele_ext`: two ideles with the same archimedean part
  and the same finite coordinates are equal. The `coord_*` and `infPart_*` lemmas compute
  them on `finiteIdeleInclusion`, `infiniteIdelesInclusion` and `integralUnitIdeles`
  (all by `rfl`).
- `integralUnitIdeles_mem`: if `H` is closed and contains the local groups outside `S`,
  then `integralUnitIdeles K u ∈ H` for every family `u` of local integral units with
  `u v = 1` for `v ∈ S`. Proof: in the product topology, `u` is a limit of families that
  agree with `u` at finitely many places and are `1` elsewhere. Such a family is a finite
  product of local units at places outside `S`, hence lies in `H`. So `u` lies in the
  closed preimage of `H`.
- `LocalUnits S`: the product of the unit groups of all archimedean completions and of the
  completions at the places in `S`. `localDiagonal S`: the diagonal map from `Kˣ`.
- `denseRange_localDiagonal`: `localDiagonal S` has dense range (weak approximation). It is
  derived from the Library's `denseRange_numberFieldFiniteCompletionDiagonal` (density of
  `K` in the product of the completions). The unit groups embed in the completions as the
  open set of nonzero coordinates (`Units.isEmbedding_val₀`), and the diagonal image of a
  nonzero element of `K` is the image of the corresponding unit.
- `localIdele S q`: the idele with archimedean and `S`-adic components `q` and all other
  finite components `1`. `continuous_localIdele`: this map is continuous.
  `localComponents S x`: the archimedean and `S`-adic components of an idele `x`, with
  `localComponents S (diagonalUnits K a) = localDiagonal S a`.
- `mul_inv_localIdele_mem`: if `H` is closed and contains the local groups outside `S`,
  then `(localIdele S (localComponents S x))⁻¹ * x ∈ H` for every idele `x`. Proof: let
  `R ⊇ S` be a finite set outside which both `x` and `x⁻¹` have integral coordinates. Then
  `x` is the product of its archimedean part, its components at the places of `R`, and an
  idele of integral units equal to `1` on `R`. Dividing by `localIdele S (localComponents S x)`
  leaves the components at `R \ S` and that unit idele, which both lie in `H`.
- `eq_top_of_isClosed` (main result). Proof: the set of `q` with `localIdele S q ∈ H` is
  closed. It contains `localDiagonal S a` for every `a : Kˣ`, because
  `diagonalUnits K a ∈ H` and `mul_inv_localIdele_mem` applies to it. By density it is
  everything. For an arbitrary idele `x`, both `localIdele S (localComponents S x)` and
  `(localIdele S (localComponents S x))⁻¹ * x` lie in `H`, hence so does `x`.
