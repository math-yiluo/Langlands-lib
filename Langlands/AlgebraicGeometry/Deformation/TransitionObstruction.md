# Obstruction cochains of families of lifted transition maps

Module `Langlands.AlgebraicGeometry.Deformation.TransitionObstruction`.

Let `R` be a local ring and `Y` a scheme over `Spec R`. This module sets up the Čech obstruction
to gluing local lifts of a scheme, as in SGA 1, Exposé III, §6. The obstruction functions are
defined for `Y` separated and smooth over `Spec R` and an elementary ideal `I`: an ideal with
`maximalIdeal R * I = 0` (an instance argument) that is contained in the maximal ideal (the
field `ideal_le` of the difference coordinates `b : Z.Coordinates I` of `ElementaryMorphismLifts`),
so that `I ^ 2 = 0`. The general lemmas on agreement modulo an ideal below take the containment or
a square-zero condition as an explicit hypothesis where they need it.

## Points of morphisms on affine opens

`pt hU g hg` is the point, on the coordinate ring `Sections Y U` of an affine open `U`, of a
morphism `g : U ⟶ Z.X` over the base. The lemmas `restrict_pt`, `restrict_ringOf_pt` and
`fibreMap_ringOf` compute it along restrictions and along morphisms of affine opens over the base
(`ringOf`); `openDifference_pt_restrict`, `openDifference_pt_ringOf` and
`openDifference_pt_comp_eq` compute the difference functions (`openDifference`, module
`ElementaryLiftCech`) of such points along restrictions, along morphisms of opens agreeing with the
inclusion on the residue fibre, and along post-composition with two maps agreeing on the residue
fibre.

`AgreeMod I hU a b` says that two morphisms out of an affine open `U` agree after reduction
modulo the ideal extended to its coordinate ring. The lemmas `AgreeMod.trans`, `AgreeMod.symm`,
`AgreeMod.comp`, `AgreeMod.of_mono`, `AgreeMod.homOfLE_comp` and `AgreeMod.ringOf_comp` transport
it along compositions and restrictions. For an ideal `L` of `R` and maps `a, b` with
`AgreeMod L hU a b`:

- `pullback_eq_of_agreeMod`: `a` and `b` agree on the base change of `U` along
  `Spec (R ⧸ L) ⟶ Spec R`;
- `comp_eq_of_agreeMod`: `u ≫ a = u ≫ b` for every map `u` into `U` lying over `Spec (R ⧸ L)`;
- `fibre_of_agreeMod`, under the hypothesis `L ≤ maximalIdeal R`: `a` and `b` agree on the actual
  residue fibre of `U`;
- `apply_eq_of_agreeMod`, under the hypothesis that the ideal `L` extended to the coordinate ring
  of `U` has square zero: `a` and `b` agree on underlying points. For an elementary ideal this
  hypothesis holds, since `L ^ 2 ≤ maximalIdeal R * L = 0`.

## Families and their obstruction

`Family Y` consists of a finite family of affine opens `V l` and transition maps
`θ l m : V l ⊓ V m ⟶ Y` that fix points, lie over the base and are the inclusion on the actual
residue fibre. On a triple overlap, `comp l m n` is `θ l m ∘ θ m n` and `direct l m n` is `θ l n`;
`Agrees I` asks them to agree modulo `I`.

For a separated smooth `Y`, a target `Z` with difference coordinates `b`, a reduction `F` of `Y`
modulo the maximal ideal, a family `D` with `D.Agrees I` and an observer `π : Y ⟶ Z.X`,
`obstruction b F hD π l m n j` is the `j`-th difference function (`openDifference`) from the
composite `π ∘ comp l m n` to the direct transition `π ∘ direct l m n`, on the residue fibre of the
triple overlap: the first argument of `openDifference` is the point of the composite and the
second the point of the direct transition.
`obstruction_four` proves the Čech identity on quadruple overlaps,
`e(m,n,p) - e(l,n,p) + e(l,m,p) - e(l,m,n) = 0` after restriction, from additivity of differences
(`openDifference_add`) and their behaviour under pre- and post-composition (`obstruction_shift`,
`obstruction_post`).

## Provenance

SGA 1, Exposé III, §6, formula (3) and the following paragraph (recomposed edition, arXiv
math/0206203v2, printed pp. 65–66, PDF pp. 81–82): the composite `f_ijk` of transition
isomorphisms is a Čech `2`-cocycle with coefficients in the sheaf of infinitesimal
automorphisms. Here the cocycle is computed in difference coordinates of lifts, through an
observer `π`.
