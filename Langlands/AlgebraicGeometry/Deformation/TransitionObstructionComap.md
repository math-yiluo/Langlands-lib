# Obstruction cochains along maps and for quotients of observers

Module `Langlands.AlgebraicGeometry.Deformation.TransitionObstructionComap`.

## Pulling back obstructions

- `pt_eq_pt` compares points of equal morphisms, and `sectionMap_pt` shows that restricting the
  point of `g : U ⟶ Z.X` along a morphism `f : Y' ⟶ Y` of schemes over the base (`sectionMap`)
  gives the point of `f|_V ≫ g` on an affine open `V ≤ f⁻¹ U`.
- Let `D` be a family on `Y` and `D'` one on `Y'` (module `TransitionObstruction`), `f : Y' ⟶ Y`,
  and indices `l m n` of `D'`, `a c e` of `D` with `D'.V l ≤ f⁻¹(D.V a)` and so on. If the
  transitions are compatible, `D'.θ l m ≫ f = f|_{…} ≫ D.θ a c` for the three pairs, then
  `comp_comap` and `direct_comap` give the same for the composites and direct transitions on the
  triple overlaps.
- `obstruction_comap`: under these hypotheses and for observers with `π' = f ≫ π`, the obstruction
  of `D'` at `(l, m, n)` is the pullback, along the reduction of `f` (`Reduction.map`), of the
  obstruction of `D` at `(a, c, e)`. The proof uses `openDifference_sectionMap` (module
  `ElementaryLiftCech`).

## Quotients of observers

For a target `Target.ofGroup H` given by a commutative group scheme `H` (module
`GroupTargetDifference`):

- `pt_mul_inv`: the point of `g ≫ (π₁ * π₂⁻¹)` is the point of `g ≫ π₁` times the inverse of the
  point of `g ≫ π₂`, since precomposition is multiplicative in the group of maps into `H.X`;
- `openDifference_div`: difference functions of quotients are differences of difference functions;
- `obstruction_mul_inv`: the obstruction of a family for the observer `π₁ * π₂⁻¹` is the
  obstruction for `π₁` minus the obstruction for `π₂`.

## Provenance

These are naturality properties of the obstruction cocycle of SGA 1, Exposé III, §6, used to
compare the obstruction of a product of schemes with that of a factor, as in the proof of
Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, Harvard thesis revised
14 March 2021, Proposition 2.2.4.1 (printed pp. 152–154, PDF pp. 180–182).
