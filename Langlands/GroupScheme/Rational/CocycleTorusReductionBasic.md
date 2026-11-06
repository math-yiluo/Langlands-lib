# Basic constructions of torus reductions of cocycles

Lean module: `Langlands.GroupScheme.Rational.CocycleTorusReductionBasic`, namespace
`Langlands.GroupScheme.Cocycle.TorusReduction`.

The structure `Cocycle.TorusReduction ξ` of the Library module
`Langlands.GroupScheme.Rational.CocycleTorusReduction` packages a finite Galois extension
`M/K` with an fpqc refinement `Spec M ⟶ U` of the cover, a cochain `c : Spec M ⟶ G`, and a
closed torus `T ⟶ G` such that `c(a)⁻¹ · ξ(a, b) · c(b)` factors through `T` for all
pairs `a, b` of points of `Spec M` over every test scheme. This module records how such
reductions behave under refinement and twisting, and constructs them for coboundaries.

## Declarations

Here `K` is a field, `G` a group scheme over `Spec K`, and `U`, `V` relative schemes over
`Spec K`.

- `ofRefine r R`: for a morphism `r : V ⟶ U` whose underlying scheme morphism is
  quasi-compact, flat and surjective, a torus reduction `R` of the refined cocycle
  `ξ.refine r` gives a torus reduction of `ξ`. It has the same Galois extension, cochain
  and torus, and refinement `R.refinement ≫ r`. The three fpqc properties pass to the
  composite because they are stable under composition.
- `ofTwist f R`: for `f : U ⟶ G.X`, a torus reduction of the twist
  `(ξ.twist f)(a, b) = f(a)⁻¹ ξ(a, b) f(b)` gives one of `ξ`, with cochain
  `(R.refinement ≫ f) · R.cochain` and everything else unchanged.
- `twist f R`: conversely, a torus reduction of `ξ` gives one of `ξ.twist f`, with
  cochain `(R.refinement ≫ f)⁻¹ · R.cochain`.
- `ofCoboundary f hf T hT i hi`: let `ξ` be a cocycle on the finite Galois cover
  `Over.mk (Spec.map (algebraMap K L))`. If `ξ(a, b) = f(a) f(b)⁻¹` for all `a, b`, then
  `ξ` reduces to any closed torus `i : T ⟶ G`. The reduction uses the identity
  refinement, the cochain `f` and unit torus values: `f(a)⁻¹ ξ(a, b) f(b) = 1`, and the
  unit composed with a group homomorphism is the unit (`MonObj.one_comp`).
- `nonempty_of_isTrivial`: if `G.X.hom` is separated, every trivial cocycle on a finite
  Galois cover has a torus reduction. The torus used is the Library's trivial torus
  `TorusExistence.trivialTorus K` (the split torus on the empty index type), embedded as
  the identity section by `TorusExistence.trivialTorusHom G`. It is a closed subgroup by
  `TorusExistence.isClosedSubgroup_trivialTorusHom`. Affine group schemes are separated
  (Mathlib instance `IsSeparated.of_isAffineHom`), so this applies to semisimple `G`.

## Proofs

The factorization equations are rearrangements in the group of points `Z ⟶ G.X`, using
`refine_toFun`, the definition of `Cocycle.twist`, `MonObj.comp_mul`, `GrpObj.comp_inv`
and the `group` tactic. Each construction keeps the given torus witness `t`.

## Provenance

Internal bookkeeping for the proof of
`Langlands.GroupScheme.QuasiSplitCocycleTorusReductionStatement`. These are the
cochain-level forms of the facts that a cohomologous cocycle, or one inflated from a
coarser cover, has the same reductions, and that a coboundary reduces to the trivial
torus. No literature statement is formalized verbatim.
