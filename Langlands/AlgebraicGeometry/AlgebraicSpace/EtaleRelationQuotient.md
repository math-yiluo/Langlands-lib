# The fppf sheaf quotient of an equivalence relation on points

Authors: Worker 1001.

Internal infrastructure for the proof of
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement`
(Stacks Project Theorem 65.10.5, Tag [02WW](https://stacks.math.columbia.edu/tag/02WW),
retained as `stacks-etale-equivalence-relations-2026-11-01`). The source writes `U/R` for
the fppf sheaf quotient of an equivalence relation without spelling out the construction.
This module constructs it as the sheafification of the presheaf quotient and proves the two
properties the proof needs. All declarations are in the namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.RelationQuotient`.

Throughout, `S : Scheme.{u}`, `U R : Over S` and `t s : R ⟶ U` are morphisms over `S`.
Points are taken in the convention of `AlgebraicSpace.Basic`: `schemeYoneda S` is the lifted
functor of points with values in `Type (u + 1)`, and `FppfSheaf S` consists of sheaves for
`fppfTopology S`.

## The relation

- `IsOverEquivRel t s` is a structure of four conditions on `T`-points for every
  `T : Over S`:
  - `ext`: a point `r : T ⟶ R` is determined by `r ≫ t` and `r ≫ s`;
  - `refl`: every `x : T ⟶ U` is `r ≫ t = x = r ≫ s` for some `r`;
  - `symm`: every `r` has a partner `r'` with `r' ≫ t = r ≫ s` and `r' ≫ s = r ≫ t`;
  - `trans`: if `r ≫ s = r' ≫ t`, there is `r''` with `r'' ≫ t = r ≫ t` and
    `r'' ≫ s = r' ≫ s`.

  This is the slice version of the relation conventions of Stacks Definition 39.3.1
  (Tag [022P](https://stacks.math.columbia.edu/tag/022P)), tested only on schemes over `S`.
- `PointRel t s T x y` says that the two `T`-points `x y` of `U` (as lifted elements
  `ULift (T ⟶ U)`) are `r ≫ t` and `r ≫ s` for some `r : T ⟶ R`. `PointRel.comp`
  shows it is stable under precomposition, and `IsOverEquivRel.equivalence` shows it is
  an equivalence relation on `T`-points when `IsOverEquivRel t s` holds.

## The quotient

- `quotientPresheaf t s` sends `T` to the quotient type `Quot (PointRel t s T)`, with
  restriction induced by precomposition.
- `quotientπ t s` is the projection from the points of `U`. It is surjective on sections
  (`quotientπ_surjective`), coequalizes `t` and `s` (`quotientπ_w`), and, under
  `IsOverEquivRel t s`, identifies two points exactly when they satisfy `PointRel`
  (`quotientπ_app_eq_iff`, via `Equivalence.eqvGen_iff`).
- `quotientSheaf t s : FppfSheaf S` is the fppf sheafification of `quotientPresheaf t s`
  (Mathlib's `presheafToSheaf`).
- `quotientMap t s` is the composite of `quotientπ t s` with the unit `toSheafify`.
  `quotientMap_w` shows that it coequalizes `t` and `s`.

## Main results

- `isLocallySurjective_quotientMap` (instance): `quotientMap t s` is fppf locally
  surjective. Its first factor is surjective on sections and its second factor is the
  sheafification unit, which is locally surjective.
- `exists_of_quotientMap_eq`: assume `IsOverEquivRel t s`. If two points `x y : T ⟶ U`
  have equal images under `quotientMap t s`, then `x = r ≫ t` and `y = r ≫ s` for some
  `r : T ⟶ R`. Proof: by Mathlib's `Presheaf.equalizerSieve_mem`, the images of `x` and
  `y` in the presheaf quotient agree on an fppf covering sieve of `T`. On each member `u`
  of that sieve the composites are related by some `k u : T' ⟶ R`. By `ext` these local
  points form a compatible family, so they glue in the represented sheaf `yoneda.obj R`
  (the fppf topology is subcanonical). The glued point projects to `x` and `y` because it
  does so locally and `yoneda.obj U` is separated.
- `isPullback_quotientMap`: assume `IsOverEquivRel t s`. Then the square with sides
  `(schemeYoneda S).map t`, `(schemeYoneda S).map s` and `quotientMap t s` twice is a
  pullback in presheaves on `Over S`; that is, the kernel pair of `quotientMap t s` is
  `(t, s)`. It is checked objectwise with `Types.isPullback_iff`: commutativity is
  `quotientMap_w`, injectivity is `ext`, and existence of the lift is
  `exists_of_quotientMap_eq`.
