# Rational characters as units of the coordinate algebra

This helper module turns rational characters of an affine group scheme into
units of its coordinate algebra. Here `k` is a field, `G` is a group scheme
over `Spec k` with affine structure morphism, and
`Coord G := Lie.coordinateAlgebra G` is the published chosen affine
coordinate algebra `O(G)`. It comes with the isomorphism
`Lie.coordinateIso G : Spec O(G) ≅ G` over `Spec k` and the bijection
`Lie.pointCoordinates G : G(A) ≃ (O(G) →ₐ[k] A)`. These are internal
lemmas supporting `CharacterLatticeProof`. They record the standard
description of characters as group-like units of `O(G)`.

## Universal point

- `universalPoint G : G(O(G))` corresponds to the identity of `O(G)` under
  `pointCoordinates`. `universalPoint_eq` identifies it with
  `(coordinateIso G).hom`.
- `affinePointMap_universalPoint_eq` and
  `pointCoordinates_affinePointMap_universalPoint`: pushing the universal
  point along an algebra map `φ : O(G) → B` gives the point with coordinates
  `φ`.
- `affinePointMap_universalPoint`: every point `x ∈ G(A)` is the image of
  the universal point along its own coordinates.

## Units

- `unit χ : O(G)ˣ` is the value of the rational character `χ` at the
  universal point, read through the published equivalence
  `Gm.affineUnitsEquiv` between `𝔾_m(A)` and `Aˣ`.
- `affineUnitsEquiv_comp`: for any point `x ∈ G(A)`, the unit `χ(x) ∈ Aˣ` is
  the image of `unit χ` under the coordinates of `x`. This follows from the
  naturality of `Gm.affineUnitsEquiv`.
- `unit_add`, `unit_zero`: `unit` sends the sum of characters (pointwise
  product) to the product of units. `unitHom` packages it as an additive
  homomorphism into `Additive O(G)ˣ`.
- `unit_injective`, `unitHom_injective`: a character is determined by its
  unit. Equal units give equal composites with the universal point, so
  `coordinateIso` gives equal scheme morphisms `G ⟶ 𝔾_m`. The published
  `hom_ext_points` then gives equal characters.

## Group-like property and independence

- `inclLeft` and `inclRight` are the two inclusions
  `O(G) → O(G) ⊗_k O(G)`. `comul G` is the comultiplication: the coordinates
  of the product of the two pushed-forward universal points in
  `G(O(G) ⊗ O(G))`.
- `comul_unit`: `comul G (unit χ) = unit χ ⊗ unit χ`. Evaluate `χ` at the
  product point. It is a homomorphism on points, and `affineUnitsEquiv_comp`
  applies to both factors.
- `nontrivial_coord`: `O(G)` is nonzero, since it has the augmentation
  `Lie.coordinateOrigin G : O(G) → k`.
- `linearIndependent_unit`: the family `χ ↦ unit χ` is `k`-linearly
  independent in `O(G)`. Its members are nonzero and group-like and pairwise
  distinct, so `CharacterLattice.linearIndepOn_of_comul` applies.
