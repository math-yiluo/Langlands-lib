# Homology sheaf systems of actual associated power complexes

Author: Worker 13.

This module constructs the homology sheaf systems of the published actual
sheaf-power and associated coefficient-power complexes. It constructs their
ordinary inverse limits and comparison, the canonical maps from homology of
the complex limits to the limits of homology, and their natural commutative
square. The genuine quotient units induce the homology-limit units, and the
comparison carries the sheaf unit to the coefficient unit.

## Inputs and conventions

Let `R : Type u` be a commutative ring, `I : Ideal R`, and
`X : Scheme.{u}`. Let `J : Type uJ` have morphisms in universe `vJ`, let
`D : J ⥤ GrpCat.{u}`, and let `Y : EquivariantDiagram D X.Etale`.
The hypothesis is `hY : ∀ j, IsFiniteGeometricTorsor X (Y.action j)`.
This is the published finite geometric torsor predicate: each deck group
is finite, the already etale cover morphism is finite and surjective, and
geometric points in one fiber differ by a unique deck translation.

The scheme, ring, module and group carriers share universe `u`.
The cover-object, cover-morphism and complex-degree universes `uJ`, `vJ`
and `uι` are independent. Fix `ι : Type uι`, an arbitrary complex shape
`c : ComplexShape ι`, and a degree `i : ι`.

Use the following notation for existing actual categories and functors:

```text
E = EquivariantDiagram D (ModuleCat R)
S = J ⥤ Sheaf X.smallEtaleTopology (ModuleCat R)
A_c : HomologicalComplex E c ⥤ HomologicalComplex S c
Q(K) : ℕᵒᵖ ⥤ HomologicalComplex S c,  n ↦ Q_n(A_c K)
P(K) : ℕᵒᵖ ⥤ HomologicalComplex S c,  n ↦ A_c(P_n K).
```

Here `A_c` is `etaleAssociatedVaryingComplexFunctor`; the two power-system
functors are `etaleAssociatedSheafComplexPowerSystems` and
`etaleAssociatedComplexPowerSystems`. The `P_n` are the actual coefficient
quotients, and the `Q_n` are sheafifications of the sectionwise quotients
`M / (I^n • ⊤)`. Both retain `R`-scalars. All power indices run over the
full `ℕᵒᵖ`, including zero, with transitions from exponent `n` to exponent
`m` for `m ≤ n`. The index `J` is retained as a cover diagram; no limit over
`J` is taken.

The category `S` is abelian by Mathlib's module-sheaf and functor-category
instances. `etaleSheafDiagramHomologyFunctor` is the actual functor

```text
H_i = HomologicalComplex.homologyFunctor S c i.
```

Its object is the homology of the actual complex in `S`, and its map is
`HomologicalComplex.homologyMap`. No homology objects or maps are supplied
as additional input. `etaleAssociatedHomologyFunctor` is `A_c ⋙ H_i`.
These are homology sheaves in `S`; for cochain shapes the grading may be
read cohomologically, but no global section functor is applied here.

## Systems and limits of homology

`etaleAssociatedSheafPowerHomologySystems` sends `K` to `Q(K) ⋙ H_i`.
`etaleAssociatedPowerHomologySystems` sends `K` to `P(K) ⋙ H_i`.
Both use Mathlib's right-whiskering functor. Thus objects, power
transitions and maps of coefficient complexes are the homology images of
the actual quotient complexes, transitions and chain maps; their
functoriality is furnished by actual functor composition.

Write `α(K) : Q(K) ⟶ P(K)` for the published
`etaleAssociatedComplexReductionSystemsComparison`. The new
`etaleAssociatedPowerHomologySystemsComparison` right-whiskers that
comparison by the functor of postcomposition with `H_i`.
Its component formula
`etaleAssociatedPowerHomologySystemsComparison_app` states that at `K,n`
it is exactly `HomologicalComplex.homologyMap (α(K).app n) i`.
The power and coefficient-chain-map naturality fields follow from
whiskering the published natural transformation.

`etaleAssociatedSheafPowerHomologyLimit` and
`etaleAssociatedPowerHomologyLimit` apply the ordinary limit functor to
these two homology-system functors. Their values are respectively
`lim (Q(K) ⋙ H_i)` and `lim (P(K) ⋙ H_i)` in `S`.
`etaleAssociatedPowerHomologyLimitComparison` applies that same limit
functor to the new homology-system comparison. Its theorem with suffix
`_π` identifies each target projection with the source projection followed
by `H_i.map (α(K).app n)`, using `limMap_π`.

## Homology of the complex limits

The definitions `etaleAssociatedSheafPowerLimitHomologyComparison` and
`etaleAssociatedPowerLimitHomologyComparison` are natural transformations
whose components are the canonical Mathlib maps

```text
λ_Q(K) = limit.post (Q(K)) H_i : H_i(lim Q(K)) → lim (Q(K) ⋙ H_i)
λ_P(K) = limit.post (P(K)) H_i : H_i(lim P(K)) → lim (P(K) ⋙ H_i).
```

`limit.post` lifts the image under `H_i` of the actual complex limit cone.
The two naturality fields specialize `limit.map_post` to the power-system
map induced by a coefficient chain map. The accompanying `_π` theorems
specialize `limit.post_π`: each composite with the exponent-`n` projection
is `HomologicalComplex.homologyMap (limit.π ... n) i`.

The theorem `etaleAssociatedPowerLimitHomologyComparison_square` is an
equality of natural transformations:

```text
H_i.map (limMap α(K)) ≫ λ_P(K)
  = λ_Q(K) ≫ limMap (Functor.whiskerRight (α(K)) H_i).
```

Here `limMap α(K)` is precisely the published
`etaleAssociatedComplexPowerLimitComparison` at `K`, and the rightmost
map is the new homology-limit comparison. The proof uses `NatTrans.ext`
and the same `limit.map_post`, now applied to `α(K)` itself.
No preservation of infinite limits by homology is used.

## Genuine quotient units

`etaleAssociatedSheafPowerHomologyCone` maps the published genuine sheaf
quotient cone of `A_c K` through `H_i`.
`etaleAssociatedPowerHomologyCone` maps the published genuine associated
coefficient quotient cone through `H_i`. Both have vertex `H_i(A_c K)`.

Let `u_Q` and `u_P` be the published sheaf and coefficient complex-limit
units. The natural homology-limit units are defined by the composites

```text
v_Q(K) = H_i.map (u_Q(K)) ≫ λ_Q(K)
v_P(K) = H_i.map (u_P(K)) ≫ λ_P(K).
```

They are `etaleAssociatedSheafPowerHomologyLimitUnit` and
`etaleAssociatedPowerHomologyLimitUnit`. Their `_eq_lift` theorems prove
that these composites are exactly the ordinary limit lifts of the two
mapped genuine quotient cones. This is `limit.lift_post`, with the actual
homology functor specified explicitly.

Their `_π` equations therefore give, at every natural exponent `n`,

```text
v_Q(K) ≫ π_n = H_i.map (sheafQuotient_n(A_c K))
v_P(K) ≫ π_n = H_i.map (A_c.map (coefficientQuotient_n(K))).
```

The quotient chain maps here are respectively
`sheafDiagramComplexPowerUnit` and `coefficientComplexPowerUnit`.
The proof rewrites the unit to its mapped-cone lift and applies
`limit.lift_π`. Thus the units preserve the original quotient maps,
including the sheafification in the sheaf quotient.

`etaleAssociatedPowerHomologySystemsComparison_unit` applies `H_i` to the
published genuine quotient-chain-map factorization. Functoriality of
`H_i` proves that the sheaf quotient on homology followed by the power
homology comparison is the associated coefficient quotient on homology.
Finally, `etaleAssociatedPowerHomologyLimitComparison_unit` proves
`v_Q ≫ homologyLimitComparison = v_P` as natural transformations. Its
proof compares all ordinary limit projections and uses the two unit
projection equations and the preceding quotient factorization.

## Provenance and scope

This is internal categorical infrastructure derived from
`AssociatedPowerComplexComparison`, `AssociatedComplexCompletion` and
`SheafDiagramAdicComplex`. It uses their actual associated complexes,
quotient complexes, systems, comparison maps and genuine quotient cones
unchanged. No new assertion is attributed to original literature.

The pinned Mathlib revision is
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0.
`Algebra.Homology.ShortComplex.HomologicalComplex` supplies the actual
homology functor and maps; `CategoryTheory.Sites.Abelian` and
`CategoryTheory.Abelian.FunctorCategory` supply the abelian instances;
`CategoryTheory.Limits.HasLimits` supplies `limit.post`, `limit.post_π`,
`limit.map_post`, `limit.lift_post` and ordinary limit functoriality.

The constructed maps are morphisms of diagrams of `R`-module sheaves.
Invertibility, preservation of infinite limits, Mittag-Leffler conditions,
exactness, derived completion, derived/global sections, global etale
cohomology, smooth or continuous group actions, lisse-adic properties,
and identification with Harris-specific objects remain separate
obligations. This construction does not replace the distinct
representation-theoretic `DivisibleSystem` interfaces.
