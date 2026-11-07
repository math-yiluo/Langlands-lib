# Cell compatibility from field-valued points

Module `Langlands.GroupScheme.CellFieldCompatibility`.

## Setting

`S` is a scheme, `G` and `H` are group schemes over `S`, `C` is an object of `Over S`,
`j : C ⟶ G.X` and `ν : C ⟶ H.X` are morphisms over `S`. From `prodOpen` on, `j.left` is an
open immersion. The Library's `CellGluing.CellCompatible j ν` (module
`Langlands.GroupScheme.OpenCellGluing`) says: for every `Z` over `S` and all `x y c : Z ⟶ C`,
if `(x ≫ j) * (y ≫ j) = c ≫ j` then `(x ≫ ν) * (y ≫ ν) = c ≫ ν`.

## Definitions

- `FieldCompatible j ν`: the same condition, required only when `Z` is `Spec K` for a field
  `K` (in universe `u`) with an arbitrary structure map `s : Spec K ⟶ S`.
- `prodMap j : C ⊗ C ⟶ G.X`: the product `(fst ≫ j) * (snd ≫ j)` of the two projections
  composed with `j`.
- `prodOpen j`: the open subscheme of `C ⊗ C` that is the preimage of the open image of `j`
  under `prodMap j`.
- `prodObj j`: this open subscheme as an object over `S`. `prodι j` is its inclusion into
  `C ⊗ C`.
- `prodLift q hq`: a morphism `q : Z ⟶ C ⊗ C` whose product `q ≫ prodMap j` lands in the cell
  (`CellGluing.InCell`) factors through `prodObj j`. `prodLift_ι` states the factorization.
- `prodCoord : prodObj j ⟶ C`: the cell coordinate of `prodι j ≫ prodMap j`, so that
  `prodCoord ≫ j = prodι j ≫ prodMap j` (`prodCoord_comp`).

## Results

- `inCell_prodι`: on `prodObj j`, the product of the two cell points lies in the cell.
- `cellCompatible_of_universal`: if the relation
  `(prodι j ≫ fst ≫ ν) * (prodι j ≫ snd ≫ ν) = prodCoord ≫ ν` holds on `prodObj j`, then
  `CellCompatible j ν`.
- `cellCompatible_of_fieldCompatible`: if `(C ⊗ C).left` is reduced, `H.X ⟶ S` is separated
  and `FieldCompatible j ν` holds, then `CellCompatible j ν`.

## Proof

`cellCompatible_of_universal`. Let `x y c : Z ⟶ C` with `(x ≫ j) * (y ≫ j) = c ≫ j`. Then
`lift x y ≫ prodMap j = c ≫ j`, so this product lies in the cell (`CellGluing.inCell_comp`).
Hence `lift x y` factors through `prodObj j`. Call the factorization `p`. Since `j` is a
monomorphism, `p ≫ prodCoord = c`. Composing the universal relation with `p` and expanding
products with `MonObj.comp_mul` gives `(x ≫ ν) * (y ≫ ν) = c ≫ ν`.

`cellCompatible_of_fieldCompatible`. `prodObj j` is an open subscheme of the reduced scheme
`(C ⊗ C).left`, so it is reduced. By `cellCompatible_of_universal` it suffices to show that two
morphisms `prodObj j ⟶ H.X` over `S` are equal. Mathlib's `ext_of_fromSpecResidueField_eq`
says that two morphisms over `S` from a reduced scheme to a scheme separated over `S` are equal
if they agree after composition with `Spec κ(w) ⟶ prodObj j` for every point `w`. For each `w`,
make `Spec κ(w)` an object over `S` through `prodObj j`, and call the residue-field point
`t : Spec κ(w) ⟶ prodObj j`. The three points `t ≫ prodι j ≫ fst`, `t ≫ prodι j ≫ snd` and
`t ≫ prodCoord` of `C` satisfy the relation for `j`, by `prodCoord_comp`. `FieldCompatible`
then gives the relation for `ν`, which is the required equality after composition with `t`.

## Provenance

This is an internal lemma for the Isomorphism Theorem over a reduced local ring
(`LocalSplitReducedIsomorphismTheoremStatement`), written for this project. It reduces the
compatibility hypothesis of the Library's open-cell gluing (`CellGluing.CellCompatible`) to field
points. In the intended use, `C` is smooth over a reduced local ring, so `C ⊗ C` is reduced by
`Langlands.AlgebraicGeometry.SmoothReducedBase`. The proof above is built from the Mathlib lemma
named there and does not follow a particular printed source.
