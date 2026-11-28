# Fibres of sheaves of modules at a point with a group action

Module `Langlands.Sheaf.PointActionModules`, namespace `Langlands.Sheaf.PointActionModules`.

Let `Φ : Point.{w} J` be a point of a site `(C, J)` (Mathlib's
`CategoryTheory.GrothendieckTopology.Point`) and let a group `G` act on its fibre functor through
a monoid map `act : G →* End Φ.fiber`. Let `Λ` be a commutative ring. This module makes the fibres
of sheaves of `Λ`-modules into `Λ`-linear representations of `G` and constructs, for a
representation `M`, the sheaf of `G`-equivariant maps to `M`, with the unit and counit relating
the two. It is the `Λ`-linear version of weil-conjectures's constructions for abelian sheaves
(`CategoryTheory.GrothendieckTopology.Point.sheafFiberAction`,
`CategoryTheory.GrothendieckTopology.Point.equivariantSheaf`, module
`WeilConjectures.CategoryTheory.Sites.Point.GroupAction`); it uses Mathlib only.

## The action on fibres

- `actHom Φ act σ : Φ ⟶ Φ` is the endomorphism of the point given by `act σ` (a morphism of points
  is a morphism of fibre functors in the opposite direction).
- `fiberAct Φ act P σ` is the induced endomorphism of the fibre `Φ.presheafFiber.obj P` of a
  presheaf `P` with values in any category with colimits of size `w`, Mathlib's
  `Point.Hom.presheafFiber`. On germs it is `[X, x, t] ↦ [X, σ • x, t]`
  (`toPresheafFiber_fiberAct`). It is the identity for `σ = 1` (`fiberAct_one`), satisfies
  `fiberAct (σ * τ) = fiberAct τ ≫ fiberAct σ` (`fiberAct_mul`), and commutes with the fibres of
  morphisms of presheaves (`presheafFiber_map_fiberAct`).
- `fiberRepresentation Φ act Λ P : Representation Λ G (Φ.presheafFiber.obj P)` is this action on
  the fibre of a presheaf of `Λ`-modules (`ModuleCat.{w} Λ`). The germ formula is
  `fiberRepresentation_toPresheafFiber`.
- `sheafFiberRep Φ act Λ : Sheaf J (ModuleCat.{w} Λ) ⥤ Rep.{w} Λ G` is the fibre functor with
  this representation; a morphism of sheaves goes to its fibre, which intertwines the actions.

## Equivariant maps

For `M : Rep.{w} Λ G`:

- `equivariantMaps Φ act Λ M X` is the `Λ`-submodule of maps `f : Φ.fiber.obj X → M` with
  `f (σ • x) = M.ρ σ (f x)`.
- `equivariantPresheaf Φ act Λ M` is the presheaf `X ↦ equivariantMaps … X`, with restriction by
  precomposition with `Φ.fiber.map`.
- `isSheaf_equivariantPresheaf`: it is a sheaf. The sheaf condition is checked on underlying
  sets (through `forget₂` to abelian groups and then to sets, which reflect limits): for a
  covering sieve `R` of `X`, every point `x` of the fibre over `X` comes from a point over some
  object of `R` (`Point.jointly_surjective`), and two such lifts come from a common object
  (`exists_of_fiber_map_eq`, from the cofilteredness of the category of elements of the fibre
  functor), so a compatible family glues to `x ↦` its value at any lift.
- `equivariantSheaf Φ act Λ M` is this sheaf, and `equivariantSheafFunctor Φ act Λ` the functor
  `Rep.{w} Λ G ⥤ Sheaf J (ModuleCat.{w} Λ)`, acting on morphisms by postcomposition
  (`equivariantMapsMap`).

## Unit and counit

- `toEquivariantSheaf Φ act Λ F : F ⟶ equivariantSheaf (sheafFiberRep F)` sends a section `t` over
  `X` to its germs `x ↦ [X, x, t]` (`toEquivariantMaps`); it is natural in `F`
  (`toEquivariantSheaf_naturality`).
- `fromEquivariantSheaf Φ act Λ M : sheafFiberRep (equivariantSheaf M) ⟶ M` is the morphism of
  representations `[X, x, f] ↦ f x`, defined on the fibre by Mathlib's
  `Point.presheafFiberDesc` (`fromEquivariantSheafHom`); it is equivariant because `f` is
  (`fiberAct_fromEquivariantSheafHom`) and natural in `M` (`fromEquivariantSheaf_naturality`).
- `sheafFiberRep_map_toEquivariantSheaf_comp_fromEquivariantSheaf`: the triangle identity
  `sheafFiberRep.map (toEquivariantSheaf F) ≫ fromEquivariantSheaf (sheafFiberRep F) = 𝟙`, checked
  on germs.

The module does not prove that the unit or the counit is an isomorphism; for the geometric point
of the spectrum of a field this is done in `Langlands.Geometry.FieldEtaleModuleSheaves`.
