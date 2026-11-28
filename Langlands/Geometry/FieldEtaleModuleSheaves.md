# Étale sheaves of modules on the spectrum of a field and discrete Galois representations

Module `Langlands.Geometry.FieldEtaleModuleSheaves`, namespace
`Langlands.Geometry.FieldEtaleModuleSheaves`.

Let `K` be a field, `Ks` a separable closure of `K` (`[IsSepClosed Ks] [Algebra.IsSeparable K Ks]`)
and `Λ` a commutative ring, all in one universe `u`, and `G = Gal(Ks/K)` with its Krull topology.
This module proves that étale sheaves of `Λ`-modules on `Spec K` (with values in
`ModuleCat.{u + 1} Λ`) are equivalent to `Rep.DiscreteContinuousRep.{u, u, u + 1} Λ G`,
weil-conjectures's category of `Λ`-representations of `G` in which every vector has an open
stabilizer, by the stalk at the geometric point `Spec Ks → Spec K` with the action of `G` by
transport of structure. This is Stacks Project, Theorem 59.56.3 (Tag 03QT), with coefficients in
`Λ`; weil-conjectures proves the case `Λ = ℤ`
(`AlgebraicGeometry.Scheme.etaleSheafEquivDiscreteContinuousRep`), and this module follows the
same proof for `Λ`-modules.

## Main results

- `equivalence K Ks Λ : Sheaf (Spec K)_ét (ModuleCat.{u + 1} Λ) ≌
  Rep.DiscreteContinuousRep.{u, u, u + 1} Λ Gal(Ks/K)`. Its functor `sheafFiberDiscreteRep` is
  `Langlands.Sheaf.PointActionModules.sheafFiberRep` at weil-conjectures's Galois point
  `AlgebraicGeometry.Scheme.galoisPoint K Ks` (the point `Spec Ks → Spec K`, with fibres lifted to
  the universe `u + 1`) and its action `AlgebraicGeometry.Scheme.galoisPointAct K Ks`, by which `σ`
  precomposes a lift with `Spec σ`; its inverse is the sheaf of equivariant maps
  `Langlands.Sheaf.PointActionModules.equivariantSheafFunctor`. The functor is `rfl`-equal to
  `sheafFiberRep` on objects (`equivalence_functor_obj_obj`).
- `forgetIso K Ks Λ`: the underlying `Λ`-module of `(equivalence K Ks Λ).functor.obj F` is
  isomorphic, naturally in `F`, to the stalk of `F` at Mathlib's point
  `AlgebraicGeometry.Scheme.pointSmallEtale (Spec Ks → Spec K)`; it is weil-conjectures's
  `GrothendieckTopology.Point.uliftSheafFiberIso`, which identifies the germ at a lift `x` with
  the germ at the lifted `ULift.up x` (`forgetIso_hom_app_toPresheafFiber`,
  `forgetIso_inv_app_toPresheafFiber`).
- `forgetIso_hom_app_ρ`: under `forgetIso`, `σ ∈ Gal(Ks/K)` sends the germ of a section `z` at a
  lift `x : Spec Ks → X` to the germ of `z` at any lift `x'` with `x' = Spec σ ≫ x`.

## The proof

1. **Open stabilizers** (`isOpen_fixed`). A stalk element is the germ of a section at a lift `x`
   of some étale `X` (Mathlib's `Point.toPresheafFiber_jointly_surjective`), and `x` is the image
   of the canonical point `x_E : Spec Ks → Spec E` under a morphism `Spec E → X`, for a finite
   subextension `E` of `Ks / K` (weil-conjectures's
   `AlgebraicGeometry.Scheme.exists_galoisPoint_fiber_map_eq`). The fixing subgroup of `E`, open in
   the Krull topology, fixes `x_E` and hence the germ, so the stabilizer `vecStabilizer` of the
   germ is open.
2. **The counit is an isomorphism on representations with open stabilizers**
   (`isIso_fromEquivariantSheaf`), by the argument of weil-conjectures's
   `isIso_galoisPoint_fromEquivariantSheaf`. Injectivity: a germ of an equivariant map `f` at
   `x = g(x_E)` with `f(x) = 0` restricts to an equivariant map on `Spec E` vanishing at `x_E`,
   hence on the whole fibre of `Spec E`, which is one `G`-orbit
   (`exists_galoisPointAct_galoisPointFiberSpec_eq`). Surjectivity: for `m ∈ M`, choose `E` finite
   with fixing subgroup inside the stabilizer of `m` (Mathlib's `krullTopology_mem_nhds_one_iff`);
   then `σ • x_E ↦ σ • m` is a well defined equivariant map on the fibre of `Spec E`, since the
   stabilizer of `x_E` is the fixing subgroup of `E`
   (`galoisPointAct_galoisPointFiberSpec_eq_iff`), and its germ at `x_E` maps to `m`.
3. **The unit is an isomorphism** (`isIso_toEquivariantSheaf`). By the triangle identity of
   `Langlands.Sheaf.PointActionModules` and step 2 applied to the stalk of `F` (step 1), the stalk
   of the unit is an isomorphism; the stalk at the Galois point reflects isomorphisms of sheaves
   of `Λ`-modules (`isIso_of_isIso_sheafFiber_map`, from weil-conjectures's conservative family
   `AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ`
   and Mathlib's `IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms`).
4. The equivalence is `CategoryTheory.Equivalence.mk` with the unit and counit isomorphisms of
   steps 2 and 3.

Two instances supply the filtered-colimit facts used for stalks of `ModuleCat.{u + 1} Λ` with
`Λ : Type u`, which Mathlib states only for modules in the universe of the ring:
`forget₂_preservesFilteredColimitsOfSize` and `forget_preservesFilteredColimitsOfSize` (the
forgetful functors to abelian groups and to sets preserve filtered colimits of size `u + 1`),
built from Mathlib's `ModuleCat.FilteredColimits.colimitCoconeIsColimit` and
`AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit`.

## External declarations

From weil-conjectures: `AlgebraicGeometry.Scheme.galoisPoint`, `galoisPointAct`,
`galoisEtaleSpec`, `galoisPointFiberSpec`, `exists_galoisPoint_fiber_map_eq`,
`exists_galoisPointAct_galoisPointFiberSpec_eq`, `galoisPointAct_galoisPointFiberSpec_eq_iff`,
`galoisPointAct_fiber_map_galoisPointFiberSpec`, `specAlgebraMap`,
`isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ` (namespace
`AlgebraicGeometry.Scheme`), `Rep.DiscreteContinuousRep`, and
`CategoryTheory.GrothendieckTopology.Point.uliftSheafFiberIso` with its germ lemma
`toPresheafFiber_uliftSheafFiberIso_hom_app`. Every declaration of this module depends only on
`propext`, `Classical.choice` and `Quot.sound` under `#print axioms`.
