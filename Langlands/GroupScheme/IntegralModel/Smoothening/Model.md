# The smoothening model `Spec B`

Module `Langlands.GroupScheme.IntegralModel.Smoothening.Model`. This module
assembles the proof of `Langlands.GroupScheme.IntegralModel.SmootheningStatement`
from the other `Smoothening` modules. Its main result reduces the statement to
the finite generation of the ring of integral functions.

Let `R` be a Henselian discrete valuation ring with algebraically closed residue
field and fraction field `K`. Let `G` be a smooth group scheme over `Spec K`, and
`M` an integral model of `G` (an affine, flat group scheme `M.group` of finite type
over `Spec R`, with an isomorphism `M.genericIso` from its generic fibre to `G`).
Let `A` be the coordinate Hopf algebra of `M.group` and
`B = integralFunctions R K A` the ring of integral functions on the generic fibre.
If `B` is finitely generated over `R`, the group scheme `Spec B` with its map to
`M.group` is a smoothening of `M` (Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach*, Appendix A.6, literature ID
`kaletha-prasad-2023-bruhat-tits-new-approach`).

The source constructs the smoothening as the last step of a tower of dilatations
(Construction A.6.1, Definition A.6.3). This module uses the ring of integral
functions instead: the ring of functions on the generic fibre that take values
in `R` at every `R`-point (compare Bruhat–Tits II, 1.7.3). The argument is
internal to this project. The only input it does not prove is finite generation
of `B`, the hypothesis `IntegralFunctionsFiniteTypeStatement.{u}`. In the source
that step is the termination Theorem A.6.2.

## Morphisms of affine spectra

For an `R`-algebra `A`, write `s_A = Spec.map (CommRingCat.ofHom (algebraMap R A))`
for the structure morphism `Spec A ⟶ Spec R`.

- `flat_specMap_iff`: `s_A` is flat iff `A` is flat over `R`.
- `locallyOfFiniteType_specMap_iff`: `s_A` is locally of finite type iff `A` is
  finitely generated over `R`.
- `smooth_specMap_iff`: `s_A` is smooth iff `A` is smooth over `R`.

Each follows from `HasRingHomProperty.Spec_iff` and the corresponding Mathlib
characterization of the property for `algebraMap`.

## Coordinates of a group scheme

Let `G` be a group scheme over `Spec R` whose structure morphism is affine.

- `isAffine_left`: the underlying scheme of `G` is affine
  (`isAffine_of_isAffineHom`). It is used as a local instance.
- `coord G` is the type of the Library coordinate Hopf algebra
  `AffineCoordinates.hopfAlgebra G`.
- `coordIso G : specA R (coord G) ≅ G` is the Library isomorphism
  `AffineCoordinates.hopfSpecIso G` from the Hopf spectrum of the coordinates.
- `isIso_coordIso_left`: its underlying morphism of schemes is an isomorphism.
- `coordIso_w`: the underlying morphism followed by the structure morphism of `G`
  is `s_{coord G}`.
- `flat_coord`: if `G` is flat over `Spec R`, then `coord G` is a flat `R`-module.
  By `coordIso_w`, `s_{coord G}` is an isomorphism followed by a flat morphism.
- `finiteType_coord`: if `G` is locally of finite type over `Spec R`, then
  `coord G` is finitely generated (Library `AffineCoordinates.algebraFiniteType`).

`smooth_generic_coord M`: if `G` is smooth over `Spec K`, then `K ⊗[R] A` is a
smooth `K`-algebra. The composite isomorphism

```
Spec (K ⊗[R] A) ≅ base change of Spec A ≅ base change of M.group ≅ G
```

is built from `HopfCoordinates.baseChangeSpecIso`, the base change of
`coordIso M.group`, and `M.genericIso`. It is an isomorphism over `Spec K`, so
`s_{K ⊗ A}` is an isomorphism followed by the smooth structure morphism of `G`.

## The model

Assume `A` is a commutative Hopf algebra over `R`, and use `specB`, `specA` and
`specInclHom` from the module `Lift`.

- `isAffineHom_specB`, `flat_specB`: the structure morphism of `specB R K A` is
  affine and flat. Flatness holds because `B` is torsion-free over the discrete
  valuation ring `R` (instance `instFlat` of the module `Hopf`).
- `locallyOfFiniteType_specB`: if `B` is finitely generated, the structure
  morphism of `specB R K A` is locally of finite type.
- `isIso_baseChange_specInclHom`: the base change of `specInclHom R K A` to
  `Spec K` is an isomorphism. It is enough to check this on underlying schemes,
  because the forgetful functors from group objects to monoid objects, to schemes
  over `Spec K`, and to schemes all reflect isomorphisms. The Library lemma
  `HopfMorphismBaseChange.tensorSpecIso_naturality` writes the underlying
  morphism as `Spec` of `K ⊗ incl : K ⊗[R] A → K ⊗[R] B` between two
  isomorphisms. That map is the isomorphism `genericEquiv R K A` of the module
  `Smoothness`.

From now on `R` is Henselian with algebraically closed residue field, and `M` is
an integral model of `G`.

- `smoothHom M : specB R K A ⟶ M.group` is `specInclHom` followed by
  `coordIso M.group`. `isIso_baseChange_smoothHom` records that its base change
  to `Spec K` is an isomorphism.
- `smoothModel M`, for `B` finitely generated, is the integral model with group
  scheme `specB R K A`. Its generic isomorphism is the base change of
  `smoothHom M` followed by `M.genericIso`.
- `smoothModelHom M : (smoothModel M).Hom M (𝟙 G)` has underlying homomorphism
  `smoothHom M`. The compatibility `generic_comm` holds by construction of the
  generic isomorphism of `smoothModel M`.

## Smoothening

`isSmoothening_smoothModel M`: if `G` is smooth over `Spec K` and `B` is finitely
generated over `R`, then `IsSmoothening M (smoothModel M) (smoothModelHom M)`.
The three clauses are proved as follows.

1. Smoothness. `K ⊗[R] A` is smooth over `K` (`smooth_generic_coord`), so `B` is
   smooth over `R` (`smooth_integralFunctions` of the module `Smoothness`). By
   `smooth_specMap_iff` the structure morphism of `Spec B` is smooth.
2. Bijection on `R`-points. An `R`-point is a morphism from `Spec R`, viewed as a
   scheme over itself by the identity, which is smooth. On points, the map
   induced by `smoothHom M` is composition with `specInclHom` followed by
   composition with the isomorphism `coordIso M.group`. The first map is
   bijective by `bijective_comp_specIncl` (module `Lift`) and the second has an
   inverse.
3. Universal property. Let `H` be a group scheme over `Spec R` with smooth
   structure morphism and `f : H ⟶ M.group` a homomorphism. The module `Lift`
   (`existsUnique_lift`) gives a unique `g : H ⟶ specB R K A` with
   `g ≫ specInclHom = f ≫ (coordIso M.group).inv`. Then
   `g ≫ smoothHom M = f`. Conversely, every `f''` with `f'' ≫ smoothHom M = f`
   satisfies the defining equation of `g` (`Iso.eq_comp_inv`), so `f'' = g`.

## Reduction theorem

`smoothening_of_finiteType (hfin : IntegralFunctionsFiniteTypeStatement.{u}) :
SmootheningStatement.{u}`.

Proof. Let `R`, `K`, `G` and `M` be as in `SmootheningStatement`. The coordinate
algebra `A` of `M.group` is a flat (`flat_coord`) and finitely generated
(`finiteType_coord`) commutative Hopf algebra over `R`, and `K ⊗[R] A` is smooth
over `K` (`smooth_generic_coord`). So `hfin` applies and `B` is finitely
generated over `R`. Then `smoothModel M` with `smoothModelHom M` is a
smoothening of `M` by `isSmoothening_smoothModel`.
