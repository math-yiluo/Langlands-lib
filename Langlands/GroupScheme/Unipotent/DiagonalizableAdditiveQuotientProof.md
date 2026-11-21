# Proof of equivariant smooth additive quotients of smooth connected unipotent groups

Worker 386. This module proves `DiagonalizableUnipotentAdditiveQuotientStatement.{u}`
(module `Unipotent.DiagonalizableAdditiveQuotientStatement`). The main theorem is
`diagonalizableAdditiveQuotient.diagonalizableUnipotentAdditiveQuotient`. It is an internal
step in the proof of the conjugacy of sections of trigonalizable groups (Task 7806). The
proof follows the three steps described in the statement's Markdown file.

## Notation

`k` is a field in universe `u` and `𝔾ₐ` is `VectorGroup.groupScheme (CommRingCat.of k) 1`.
`Λ` is an abelian group, `𝔻` is the diagonalizable group `D(Λ)`, and `a` is an automorphic
action of `𝔻` on a group scheme `U` over `Spec k`. For a `k`-algebra `A`, an affine point of
a group scheme `G` is a morphism `Spec A ⟶ G` over `Spec k` (`Lie.AffinePoints G A`), and
`Lie.affineMap G φ` changes the coefficients of such a point along `φ : A →ₐ[k] B`.

- `coord x ∈ A` is the coordinate of an affine point `x` of `𝔾ₐ`, read off through the
  natural vector coordinates `vectorAffineCoordinates`. `ofCoord c` is the point with
  coordinate `c`. The coordinate is injective (`coord_injective`), additive (`coord_mul`) and
  natural in `A` (`coord_naturality`).
- `Diagonalizable.Averaging.point Λ A` is the universal point `P` of `𝔻` with coefficients in
  the group algebra `A[Λ]`, and `Diagonalizable.Averaging.const Λ A : A → A[Λ]` is the
  inclusion of coefficients.

## Step 1: a smooth homomorphism to `𝔾ₐ`

`exists_smooth_hom`: let `k` be algebraically closed and `U` smooth, affine over the base,
connected, unipotent and nontrivial (`SubgroupFunctor.range (𝟙 U) ≠ ⊥`). Then there is a
homomorphism `g : U ⟶ 𝔾ₐ` whose underlying morphism of schemes is smooth.

Proof. `Unipotent.algebraicallyClosedSplit` gives a split series of some length `n`. If
`n = 0`, the series shows that `U` is trivial, which contradicts `hne`. Otherwise the last
step of the series gives a closed immersion `j : K ⟶ U` with `K` smooth, a quotient map
`q : U ⟶ V` that is an fppf quotient by `K`, and an isomorphism `V ≅ 𝔾ₐ`
(`IsVectorGroupOfDimension.iso`). The map `q` is quasi-compact because `U` is affine over the
base. `IsFppfQuotient.smooth_of_smooth_kernel` shows that `q` is smooth, so
`g = q ≫ (V ≅ 𝔾ₐ)` is smooth.

## Step 2: weight components

Let `g : U ⟶ 𝔾ₐ` be any homomorphism. For an affine point `u` of `U` with coefficients in
`A`, the coaction of `u` is

`coaction u = coord (g (P · u)) ∈ A[Λ]`,

where `u` is first viewed as a point with coefficients in `A[Λ]` through `const`. So
`coaction u = Σ_m (coaction u)_m e_m`, and this is the expansion of `d ↦ g (d · u)` in the
characters of `𝔻`. The weight-`m` component of `u` is the point
`component m u = ofCoord ((coaction u)_m)` of `𝔾ₐ`. The following lemmas hold.

- `coaction_naturality`, `component_naturality`: both are natural in `A`.
- `coaction_mul`, `component_mul`: `coaction (u v) = coaction u + coaction v`, because the
  action is by group automorphisms and `g` is a homomorphism. So each component is additive.
- `augmentation`: the `k`-algebra map `A[Λ] → A` that sends every `e_m` to `1`.
  `augmentation_apply` says it is the sum of the coefficients, `augmentation_const` says it
  is the identity on constants, and `affineMap_augmentation_point` says it sends `P` to the
  identity point of `𝔻`.
- `coord_comp_eq_augmentation`: `coord (g u) = augmentation (coaction u)`, so `g` is the
  sum of its components. Applying `augmentation` to `P · u` gives `1 · u = u`.
- `coaction_act`: for an affine point `d` of `𝔻`, `coaction (d · u)` is the translation of
  `coaction u` by the characters of `d`
  (`Diagonalizable.Averaging.translation`). The proof uses `P · (d · u) = (d P) · u` (points of
  `𝔻` commute) and `Diagonalizable.Averaging.translation_point`, which says that translating
  the coefficients of `P` by `d` gives `d P`. By `coeff_translation` the `m`-th coefficient
  is multiplied by `d(m)`.

`componentMor m : U.X ⟶ 𝔾ₐ.X` is the morphism of schemes with these values on affine points
(`PointedCoordinateWeights.homOfAffinePoints`, which uses that `U` is affine over the base).
`comp_componentMor` says `u ≫ componentMor m = component m u`. Additivity on the universal pair
of points of `U × U` (`componentMor_mul_universal`, proved with `affine_hom_ext`) gives
additivity on all points (`componentMor_mul`), so `componentMor m` underlies a homomorphism
`componentHom m : U ⟶ 𝔾ₐ` (`homOfPoints`; `componentHom_hom` identifies the underlying
morphism).

Equivariance. Let `χ_m = DiagonalizableCharacter.evalCharacter (CommRingCat.of k) Λ m` be the
character `d ↦ d(m)` of `𝔻`. `componentMor_equivariant` says that for every test scheme `T`,
every `d : T ⟶ 𝔻` and every `x : T ⟶ U`,

`a.act d x ≫ componentMor m = (VectorGroup.weightAction χ_m).act d (x ≫ componentMor m)`.

It is first proved on the universal pair of points of `𝔻 × U`
(`componentMor_equivariant_universal`) with `affine_hom_ext`. On affine points it reduces to
`coord_injective` and three facts:

- `coaction_act` and `coeff_translation` for the left side;
- `coord_weightAction_act`: the coordinate of the action of `d` through a character `χ` is the
  value of `χ` at `d` times the coordinate;
- `charValue_evalCharacter`: the value of `χ_m` at an affine point `d` is the unit `d(m)` of
  `A` given by `Diagonalizable.Averaging.pointsEquiv`.

## Step 3: some component has surjective differential

`exists_component_surjective`: if `U` is affine over the base and `g` is smooth, then some
`m` has `Lie.targetMapLinear (componentHom m) k` surjective. Here `Lie.targetMapLinear f k` is
the differential of `f` at the identity, acting on the Lie kernels of points with
coefficients in the dual numbers `k[ε]`.

Proof. The Lie kernel of `𝔾ₐ` is one-dimensional: by `lieKernel_ext`, its points are
determined by the `ε`-part of their coordinate. By `coord_smul_snd`, the `ε`-part of `c • x`
is `c` times the `ε`-part of `x`. Since `g` is smooth, its differential is surjective
(`Lie.targetMapLinear_surjective_of_smooth`), so some Lie kernel point `X` of `U` has
`g(X)` with coordinate `ε` (`vectorLiePoint` with coordinate `1`). By
`coord_comp_eq_augmentation`, the coordinate of `g(X)` is the sum of the coefficients of
`coaction X`. So the `ε`-parts of these coefficients sum to `1`, and some coefficient
`(coaction X)_m` has nonzero `ε`-part `c`. The image of `X` under `componentHom m` has
coordinate `(coaction X)_m`. A Lie kernel point `W` of `𝔾ₐ` whose coordinate has `ε`-part `w`
is then the image of `(w c⁻¹) • X`.

## Main theorem

`diagonalizableUnipotentAdditiveQuotient : DiagonalizableUnipotentAdditiveQuotientStatement.{u}`.
Step 1 gives a smooth `g : U ⟶ 𝔾ₐ`, and Step 3 gives `m` such that `componentHom m` has
surjective differential. `𝔾ₐ` is smooth (`smooth_additive`), connected
(`connectedSpace_additive`) and affine over the base, so
`Lie.smoothSurjectiveOfSurjectiveDifferential` shows that `componentHom m` is smooth and
surjective. Take `χ = χ_m` and `f = componentHom m`; equivariance is
`componentMor_equivariant`.

The hypothesis `LocallyOfFiniteType U.X.hom` of the statement is not used.

## Provenance

Internal. The statement and this proof route are formulated for Task 7806; see the
provenance section of `Unipotent.DiagonalizableAdditiveQuotientStatement`. The existence
of the split series is the Library's `Unipotent.algebraicallyClosedSplit` (SGA 3, Exp. XVII,
Corollaire 4.1.3, over an algebraically closed field). The weight decomposition of `g` uses
the Library's averaging machinery for diagonalizable groups
(`Torus/DiagonalizableAveraging.lean`). The last step uses the Library's
`Lie.smoothSurjectiveOfSurjectiveDifferential`.
