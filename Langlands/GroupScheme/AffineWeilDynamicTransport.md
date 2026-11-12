# Dynamic subgroups of actual affine Weil restrictions

Author: Worker 207.

This supporting module works with a finite projective ring map `A → B` and an
affine, locally finite type group scheme `G` over `Spec B`. Here
`R(G) = AffineWeil.groupScheme A B G` is the actual affine Weil restriction.
For a cocharacter `χ : 𝔾_m → G`, the published `AffineWeil.cocharacter A B χ`
is its restricted cocharacter of `R(G)`. The published
`AffineWeilDynamics` module proves one inclusion. A point `x : T → R(G)` lies
in the dynamic parabolic `P(cocharacter χ)` (respectively the identity-limit
subgroup `U(cocharacter χ)`) when its comparison point
`testPointsEquiv x : tensorTest T → G` lies in `P(χ)` (respectively `U(χ)`).
This module proves the converse on the points needed. It then derives the
transport of representing homomorphisms and the descent of cocharacters.
The results are internal to the Library and add no external assertion.

## Splitting curves

`lineSplit` and `gmSplit` identify `groundTest (Z × 𝔸¹_B)` with a map to
`groundTest Z × 𝔸¹_A` (respectively for `𝔾_m`) through the scalar points of
`AffineWeilCounit`. Two lemmas make them compatible with the inclusion
`𝔾_m → 𝔸¹` and with the zero sections.

`counitExtension e` takes a ground-base curve `e : groundTest Z × 𝔸¹_A → R(G)`
to the extension-base curve
`counit ≫ testPointsEquiv (lineSplit ≫ e) : Z × 𝔸¹_B → G`. Its properties:

- `isOrbitExtension_counitExtension`: if `e` extends the restricted orbit map
  of `g`, then `counitExtension e` extends the orbit map of
  `counit ≫ testPointsEquiv g`.
- `evalZero_counitExtension`: its value at `0` is the counit of the value of
  `e` at `0`.

## The converse on standard tests

On a standard test `Spec C`, `counit_testPointsEquiv_unit` shows that
`counit ≫ testPointsEquiv (testUnit ≫ x) = testPointsEquiv x`. It follows
from the triangle identity. Hence:

- `testPointsEquiv_mem_parabolic_of_standard`: if
  `g ∈ P(cocharacter χ)(Spec C)`, then `testPointsEquiv g ∈ P(χ)`.
- `testPointsEquiv_mem_unipotent_of_standard`: the same for the
  identity-limit subgroup, via `hasLimit_testPointsEquiv_of_standard`.

## Transport of representatives

- `testPointsEquiv_comp_map` identifies the comparison point of
  `x ≫ AffineWeil.map f` with `testPointsEquiv x ≫ f`. The instance
  `mono_map` shows that restriction preserves monomorphisms.
- `range_map_eq` is the general criterion. Let `f : P → G` have range `F`,
  and let `F'` be a subgroup functor of `R(G)` represented by `q : Q → R(G)`.
  Assume that `F'` contains every point whose comparison lies in `F`, and
  that the comparison of the universal point `q` lies in `F`. Then the range
  of `AffineWeil.map f` is `F'`.
- `range_map_eq_parabolic`, `range_map_eq_unipotent` and
  `isRepresentedBy_map_parabolic`, `isRepresentedBy_map_unipotent` apply
  this criterion. They use the published corepresented representatives
  `Corepresented.parabolicHom`/`unipotentHom` of `R(G)`, whose universal
  points live on standard tests. If `f` represents `P(χ)` (respectively
  `U(χ)`), then `AffineWeil.map f` represents `P(cocharacter χ)`
  (respectively `U(cocharacter χ)`).

## Descent of cocharacters

Let `ν : 𝔾_{m,A} → R(G)` be a ground-base cocharacter. `descendPoints ν`
sends `y : Z → 𝔾_{m,B}` to `counit ≫ testPointsEquiv (gmRestrict y ≫ ν)`.
These maps are monoid homomorphisms, natural in `Z`. `descendCocharacter ν`
is the resulting homomorphism `𝔾_{m,B} → G`, built with the published
`homOfPoints`. `cocharacter_descendCocharacter` proves
`cocharacter A B (descendCocharacter ν) = ν`. It is first checked on
standard tests through `gmRestrict_scalarGmPoints` and the triangle
identity. It then extends to every test because each `𝔾_m`-point factors
through its affinization (`affinization_gmAffine`, `hom_ext_points`).
Thus every cocharacter of the restricted group comes from a cocharacter of
`G`.
