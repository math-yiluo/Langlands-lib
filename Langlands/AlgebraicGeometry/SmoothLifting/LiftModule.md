# The module of lifts with a chosen base lift

Namespace `Langlands.AlgebraicGeometry.SmoothLifting`. `GLift f I x₀ s` is
the type of global lifts (see `SmoothLifting.GlobalComb`). For a
square-zero ideal `I` and a base lift `e`, `LiftModule hI e` is the same
type with the following `C`-module structure:
- zero `e`;
- addition `x + y = e + (x - e) + (y - e)`;
- scalar multiplication `c • x = e + c (x - e)`.

All three are the two-term global combination `LiftModule.lin`.

## Construction

- `Chart.grep` is the chart representative of a restricted global lift.
- `Chart.grep_gcomb` gives the representative of a combination as the
  pointwise affine combination of the representatives.
- `IsGlobalLift.ext_grep` says that representatives on a covering chart
  family determine a global lift.
- `LiftModule.coord` maps a lift to the differences of its
  representatives from those of `e`, on a chosen covering chart family
  (`LiftModule.charts`). It is injective (`coord_injective`) and turns
  `lin` into a linear combination (`coord_lin`).
- The `AddCommGroup` and `Module C` instances (`instModuleLift`) are pulled
  back along `coord` with `Function.Injective.addCommGroup` and
  `Function.Injective.module`.
- `LiftModule.lin_self` says that a combination of the base lift with
  itself is the base lift.
- `LiftModule.smul_eq_zero_of_mem` says that elements of `I` act by zero,
  because differences of representatives lie in the square-zero ideal
  `I R`.

## Morphisms

For `φ : X ⟶ Y` over `S` with `x₀ ≫ φ = x₀Y` and `e ≫ φ = eY`:
- `GLift.map` and `gcomb_map` transport lifts and combinations;
- `LiftModule.lin_map` is the two-term case;
- `LiftModule.map` is the induced `C`-linear map
  `LiftModule hI e →ₗ[C] LiftModule hI eY`, composition with `φ`.

`gcomb_congr` rewrites combinations along equalities of their inputs.

## Provenance

These are internal constructions for the lifting of homomorphisms from
groups of multiplicative type through nilpotent thickenings. They give
the set of infinitesimal lifts with a base point its module structure, as
in the torsor description of Stacks Project, More on Morphisms,
Lemma 37.11.7 (Tag 02H6).
