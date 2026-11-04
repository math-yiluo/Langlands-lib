# A torus action on a vector group as an abstract point action

This module is an internal step in the proof that every torus action on a vector
group becomes linear in suitable coordinates. It packages a concrete torus action
as an instance of the abstract structure `TorusLinearization.PointAction`. The
positive-characteristic linearization argument is carried out for that abstract
structure. Everything is in namespace `Langlands.GroupScheme.RelativeRoot`.

## Data

Fix fields `k ⊆ K`, a group scheme `T` over `k` with a splitting
`s : T_K ≅ splitTorus (Spec K) I` (`I` finite), a group scheme `V` over `k`, an
action `a` of `T` on `V`, and natural coordinates `e` of `V` of dimension `n`
(`he : IsNaturalVectorCoordinates e`).

`torusPointAction s a he : PointAction k K I n` has the following fields:

- the points over a `k`-algebra `B` are `Lie.AffinePoints T B`, the points of `T`
  over `Spec B`; algebra maps act by `Lie.affineMap`, which satisfies the identity
  and composition laws `Lie.affineMap_id` and `Lie.affineMap_comp`;
- a point `t` acts on coordinate vectors by `coordinateAction a e t`, the action of
  `t` on the points of `V` read in the coordinates `e`. It is additive because it
  is an additive map. It commutes with extension of coefficients by
  `coordinateAction_naturality he`;
- over an algebra `C` over `K`, a family of units `τ : I → Cˣ` gives the point
  `splitPoint s τ`. Every point arises this way (`splitPoint_surjective`), the
  construction is natural in `K`-algebra maps (`splitPoint_naturality`), and the
  identity and product laws for the action follow from `splitPoint_one`,
  `splitPoint_mul`, `coordinateAction_one` and `coordinateAction_mul`.

`torusPointAction_act` records that the abstract action is the coordinate action.

## Provenance

This adapter is internal to the proof of `TorusVectorActionLinearizationStatement`.
It does not formalize a statement from the literature. It records the passage
from a torus action on a vector group to an action on coordinate vectors described
on points over a splitting field. This passage belongs to the project's own
derivation. Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, 2nd ed., Theorem B.4.3
and Propositions B.4.1–B.4.2 (printed pp.575–577, PDF pp.601–603) work directly with
the group and an equivariant embedding into a linear representation, not with
points in coordinates.
