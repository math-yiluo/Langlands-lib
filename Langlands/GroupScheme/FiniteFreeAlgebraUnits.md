# Unit group schemes of finite free algebras over a commutative ring

Let `R` be a commutative ring (a `CommRingCat.{u}`), let `A : Type u` be an
associative unital `R`-algebra, and fix a finite basis
`b : Module.Basis (Fin n) R A`. The algebra `A` may be noncommutative, and it
may be the zero algebra (`n = 0`). This module builds a smooth affine group
scheme `groupScheme b` over `Spec R` whose points on a scheme `T` over
`Spec R` are the units of `Γ(T) ⊗[R] A`. It also proves:

- every fibre is geometrically irreducible and geometrically connected;
- the construction commutes with base change;
- isomorphic algebras give isomorphic group schemes, whatever bases are
  chosen;
- for `A = M_N(R)` the group scheme is the Library's
  `GeneralLinear.groupScheme (Fin N) R`.

## Provenance

The module is derived. It generalizes the published
`Langlands.GroupScheme.FiniteAlgebraUnits`, which does the same construction
over a field `k`. The construction there (polynomial coordinates, the
determinant of left multiplication by the generic element, the
away-localization at that determinant, and the corepresentation of
`S ↦ (S ⊗ A)ˣ`) is in turn adapted from the published
`Langlands.AlgebraicGeometry.Units.FiniteAlgebraDeterminant` and
`Langlands.AlgebraicGeometry.Units.FiniteAlgebraAffine`.

The field module cannot be applied over a ring such as `𝒪`. Its base is
`Spec k` for a field `k`. About seventy Library modules use it, so it is not
edited in place. This module repeats its coordinate construction with the
field `k` replaced by `R`. The declarations from `genericElement` to
`corepresentableBy` have the same names and the same proofs as there, with
`k` replaced by `R` (and the test algebra renamed `S`). None of those proofs
used that `k` is a field. The field module's `determinant_eq_det`,
`candidate`, `determinant_rank_zero` and `candidate_smooth` are not repeated;
smoothness is the instance `candidateRing_smooth` here, proved from Mathlib's
`Algebra.Smooth.of_isLocalization_Away` and `Algebra.Smooth.comp`. The
field module's `rationalPointsEquiv` does use the field (through a Galois
point comparison). Here it is replaced by `sectionUnitsEquiv`, which uses the
Library's `WeilGm.selfSectionsAlgEquiv` and works over any `R`. The
following parts are new: affineness of the structure morphism, flatness and
local finite type, base change, geometric irreducibility and connectedness,
`congrIso` and `generalLinearIso`. The Lean proofs are written here from
Mathlib and the Library; no external code is adapted.

This module is the first step towards a model-level non-hyperspecial
parahoric for `GL_N`, for the task objective's comparison of a hyperspecial
with a non-hyperspecial parahoric (Task 3557). The planned next unit takes
`A` to be the standard Iwahori order in `M_N(𝒪)`, which is free over `𝒪`
but is not an algebra over a field. Kaletha–Prasad, *Bruhat–Tits Theory: A
New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`
(SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`),
§15.1.33 (printed p. 524 / PDF p. 555), describes `G(k)^0_F` for
`G = GL(X)` and a periodic lattice chain as the subgroup stabilizing each
lattice of the chain. The authors' corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`) do not
amend Chapter 15. This module makes no claim about lattice chains,
parahoric subgroups or KP's objects. Its statements are about arbitrary
finite free algebras over arbitrary commutative rings.

## Setting

The module imports from the Library:

- `Langlands.GroupScheme.CorepresentedPoints` (`Corepresented.groupScheme`,
  `Corepresented.pointsEquiv` and its naturality);
- `Langlands.GroupScheme.CorepresentedSmoothGeometry` (`surjective_hom`: the
  structure morphism of a group scheme is surjective);
- `Langlands.GroupScheme.Torus.WeilRestrictionBaseChange` (`WeilGm.baseMap`,
  `WeilGm.restrictedSections` and its `R'`-algebra instances,
  `GroupScheme.baseChangePointsEquiv`, `isoOfPointModels`);
- `Langlands.GroupScheme.Torus.WeilRestrictionIntegralModel`
  (`WeilGm.selfSectionsAlgEquiv`);
- `Langlands.GroupScheme.GeneralLinear` (`GeneralLinear.groupScheme`,
  `GeneralLinear.pointsEquiv` and its naturality);
- `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected`
  (`GeometricallyIrreducible.geometricallyConnected`). This module imports
  all of Mathlib.

It names the Mathlib modules `Mathlib.RingTheory.MatrixAlgebra`
(`matrixEquivTensor`), `Mathlib.LinearAlgebra.Matrix.StdBasis`
(`Matrix.stdBasis`), `Mathlib.AlgebraicGeometry.AffineSpace` and
`Mathlib.AlgebraicGeometry.Geometrically.Connected`/`Irreducible`.

All rings, algebras and schemes are in one universe `u`. Everything is in the
namespace `Langlands.GroupScheme.FiniteFreeAlgebraUnits`. The test algebras
`S`, `S'`, `B`, `C` are commutative `R`-algebras; only `A` (and `A'` below)
may be noncommutative. `algΓ R` is Mathlib's relative global-sections
functor, so `((algΓ R).obj T).unop` is `Γ(T)` as an `R`-algebra.

## Declarations

### Coordinates and the universal unit

- `coordinateRing R n` (abbreviation): `MvPolynomial (Fin n) R`.
- `genericElement b`: `∑ i, X i ⊗ b i` in `coordinateRing R n ⊗[R] A`.
- `determinant b`: `Algebra.norm (coordinateRing R n) (genericElement b)`,
  the determinant of left multiplication by the generic element.
  `determinant_eq_matrix_det` writes it as the determinant of the
  multiplication matrix in the base-changed basis. No identification with a
  reduced norm is claimed.
- `candidateRing b` (abbreviation): `Localization.Away (determinant b)`.
- `localizedGenericElement b` and `localizedGenericElement_eq_sum`: the
  generic element in `candidateRing b ⊗[R] A`.
- `leftMulMatrix_map`, `norm_map`: for `φ : S →ₐ[R] C`, multiplication
  matrices and the norm commute with the coefficient change
  `φ ⊗ id_A`.
- `localizedGenericElement_isUnit`, `algebraicUniversalUnit b` (with
  `algebraicUniversalUnit_val`): the localized generic element is a unit.
- `candidateRing_smooth` (instance): `Algebra.Smooth R (candidateRing b)`.

### Corepresentation

- `evaluatedElement`, `evaluatedElement_eq_sum`, `evaluatedElement_repr`,
  `evaluatedElement_injective`, `coefficientMap`,
  `evaluatedElement_coefficientMap`, `norm_evaluatedElement`,
  `coefficientMap_determinant_isUnit`, `unitCoefficientMap`,
  `unitCoefficientMap_algebraMap`, `algebraicPoint`, `algebraicPoint_val`,
  `algebraicPoint_unitCoefficientMap`, `algebraicPoint_injective`: the two
  directions between `R`-algebra maps `candidateRing b → B` and units of
  `B ⊗[R] A`.
- `algebraicPointEquiv b : (candidateRing b →ₐ[R] B) ≃ (B ⊗[R] A)ˣ` and its
  naturality `algebraicPoint_comp`.
- `functor R A : CommAlgCat R ⥤ GrpCat`: `S ↦ (S ⊗[R] A)ˣ`, with maps
  induced by `f ⊗ id_A`.
- `coordinateAlgebra b` (abbreviation) and `corepresentableBy b`: the
  coordinate algebra corepresents the underlying set-valued functor.

### The group scheme

- `groupScheme b` (abbreviation, the declared definition of this unit):
  `Corepresented.groupScheme (functor R A) (corepresentableBy b)`, a group
  scheme over `Spec R`.
- `groupScheme_hom`: its structure morphism is
  `Spec.map (CommRingCat.ofHom (algebraMap R (candidateRing b)))`
  (by `rfl`).
- Instances: `groupScheme_isAffine` (the total space is affine),
  `groupScheme_isAffineHom`, `groupScheme_smooth` (from the theorem `smooth`),
  `groupScheme_flat`, `groupScheme_locallyOfFiniteType`.
- `pointsEquiv b T : (T ⟶ (groupScheme b).X) ≃* (Γ(T) ⊗[R] A)ˣ` for every
  `T : Over (Spec R)`, and `pointsEquiv_naturality`: restriction along
  `T' ⟶ T` is the unit map of `Γ(T) → Γ(T')` tensored with `id_A`.
- `sectionTensorEquiv : Γ(Spec R) ⊗[R] A ≃ₐ[R] A` and
  `sectionUnitsEquiv b : rationalPoints (groupScheme b) ≃* Aˣ`.

### Base change

Let `R'` be a `CommRingCat.{u}` with `[Algebra R R']`.

- `baseChangeTensorEquiv A R' S : S ⊗[R] A ≃+* S ⊗[R'] (R' ⊗[R] A)` for an
  `R'`-algebra `S` with `IsScalarTower R R' S`, sending `s ⊗ a` to
  `s ⊗ (1 ⊗ a)` (`baseChangeTensorEquiv_tmul`). `baseChangeTensorEquiv_natural`:
  it commutes with maps of `R'`-algebras.
- `basePointsEquiv b R' T` (with `basePointsEquiv_apply` and
  `basePointsEquiv_naturality`): points of the base change along
  `WeilGm.baseMap R R' : Spec R' ⟶ Spec R` are units of
  `Γ(T) ⊗[R'] (R' ⊗[R] A)`.
- `baseChangeIso b R'`:
  `(GroupScheme.baseChange (WeilGm.baseMap R R')).obj (groupScheme b) ≅
  groupScheme (b.baseChange R')`, built with `isoOfPointModels`.
  `baseChangeIso_hom_points`: on points it is `basePointsEquiv`.

### Geometric irreducibility and connectedness

- `geometricallyIrreducible_spec_mvPolynomial (m : Type u)`: the structure
  morphism `Spec (MvPolynomial m R) ⟶ Spec R` is geometrically irreducible.
- `geometricallyIrreducible_spec_coordinateRing n`: the same for
  `coordinateRing R n`, whose variables are indexed by `Fin n : Type`.
- `groupScheme_hom_eq_comp`: the structure morphism factors as
  `Spec (candidateRing b) ⟶ Spec (coordinateRing R n) ⟶ Spec R`.
- `geometricallyIrreducible` (instance):
  `GeometricallyIrreducible (groupScheme b).X.hom`.
- `geometricallyConnected` (instance):
  `GeometricallyConnected (groupScheme b).X.hom`. For an integral model
  whose group is `groupScheme b`, this is the Library's
  `HasGeometricallyConnectedFibres`, which
  `IntegralModel.hasConnectedFibres_of_geometricallyConnected` turns into
  connected fibres.

### Change of algebra

Let `A'` be another `R`-algebra with basis `b' : Module.Basis (Fin m) R A'`,
and `e : A ≃ₐ[R] A'`.

- `tensorCongr_map`: `id ⊗ e` commutes with `f ⊗ id` for `f : S →ₐ[R] S'`.
- `congrPointsEquiv b e T : (T ⟶ (groupScheme b).X) ≃* (Γ(T) ⊗[R] A')ˣ` and
  `congrPointsEquiv_naturality`.
- `congrIso b b' e : groupScheme b ≅ groupScheme b'`, and
  `congrIso_hom_points`: on points it is the unit map of `id ⊗ e`. Taking
  `e = AlgEquiv.refl` shows that the group scheme does not depend on the
  basis up to isomorphism.

### The matrix algebra

Let `N : ℕ`.

- `matrixBasis R N`: the matrix-unit basis `Matrix.stdBasis` of
  `Matrix (Fin N) (Fin N) R`, reindexed by `finProdFinEquiv` to
  `Fin (N * N)`.
- `matrixEquivTensor_symm_map`: Mathlib's identification
  `S ⊗[R] M_N(R) ≃ M_N(S)` (the inverse of `matrixEquivTensor`) commutes with
  coefficient changes.
- `matrixPointsEquiv R N T : (T ⟶ (groupScheme (matrixBasis R N)).X) ≃*
  GL (Fin N) Γ(T.left, ⊤)` and `matrixPointsEquiv_naturality`: restriction
  is entrywise pullback of global sections.
- `generalLinearIso R N :
  groupScheme (matrixBasis R N) ≅ GeneralLinear.groupScheme (Fin N) R`, and
  `generalLinearIso_hom_points`: on points it is `matrixPointsEquiv`.

## Proof outline

**Universal unit.** The multiplication matrix of `(φ ⊗ id) x` is the
entrywise image of that of `x` (tensor induction), so the norm commutes with
coefficient changes. The norm of the localized generic element is the image
of `determinant b`, a unit in `candidateRing b`. By
`LinearMap.isUnit_iff_isUnit_det`, left multiplication is invertible, and
Mathlib's `Algebra.lmul_isUnit_iff`, which needs no commutativity of `A`,
makes the element a unit. For `n = 0` the determinant is the empty
determinant `1`.

**Points.** A map `candidateRing b → B` gives a unit by specializing the
universal unit. Conversely the coefficients of a unit `x` of `B ⊗[R] A` in
the base-changed basis define a map `coordinateRing R n → B`. It sends
`determinant b` to the norm of `x`, which is a unit; so the map extends to
the away-localization. Uniqueness of basis coordinates and of localization
maps give both inverse laws. The group scheme, its point equivalence and its
naturality then come from the Library's corepresented group-scheme
construction.

**Smoothness and finiteness.** A polynomial ring is smooth and an
away-localization is smooth, so `candidateRing b` is smooth over `R`. Mathlib's
`HasRingHomProperty.Spec_iff` and `RingHom.smooth_algebraMap` give smoothness
of the structure morphism. Flatness and local finite type follow from
smoothness. The structure morphism is the spectrum of a ring map, hence
affine.

**Base change.** `baseChangeTensorEquiv` is the composite of
`S ⊗[R] A ≃ (S ⊗[R'] R') ⊗[R] A` and associativity. Its naturality is proved by
tensor induction. The base-change point equivalence composes the Library's
`GroupScheme.baseChangePointsEquiv` with `pointsEquiv` over `Spec R` and this
ring isomorphism. The Library's `isoOfPointModels` turns the two natural
point models into an isomorphism.

**Geometric irreducibility.** Mathlib proves that affine space
`𝔸(m; Spec R) ⟶ Spec R` is geometrically irreducible, for `m : Type u`.
`AffineSpace.SpecIso_inv_over` identifies it with
`Spec (MvPolynomial m R) ⟶ Spec R` up to an isomorphism, and geometric
irreducibility is stable under base change, so it respects isomorphisms. For
`Fin n`, `MvPolynomial.renameEquiv` with `Equiv.ulift` identifies
`coordinateRing R n` with `MvPolynomial (ULift (Fin n)) R`. The structure
morphism of `groupScheme b` is the open immersion
`Spec (candidateRing b) ⟶ Spec (coordinateRing R n)` (Mathlib's instance for
away-localizations) followed by the geometrically irreducible map to
`Spec R`. It is surjective because every group scheme has a unit section
(`surjective_hom`). Mathlib's instance for a surjective open subscheme of a
geometrically irreducible scheme then applies. Geometric connectedness
follows from the Library's `GeometricallyIrreducible.geometricallyConnected`.

**Change of algebra and matrices.** In both cases the two point models are
units of `Γ(T) ⊗[R] A'`, respectively `GL_N(Γ(T))`, and the needed
naturality reduces, by tensor induction, to `id ⊗ e` commuting with `f ⊗ id`,
respectively to `(s • M.map (algebraMap R S)).map f =
f s • M.map (algebraMap R S')` for an `R`-algebra map `f`. The Library's
`GeneralLinear.pointsEquiv_naturality` supplies the naturality on the
`GL_N` side, and `isoOfPointModels` gives the isomorphisms.

## Non-claims

- The module does not construct an Iwahori order, a lattice chain or any
  parahoric group scheme, and it does not identify `groupScheme b` with a
  Bruhat–Tits group scheme. It builds no `IntegralModel`.
- It does not compare `groupScheme b` with the published field module
  `Langlands.GroupScheme.FiniteAlgebraUnits` when `R` is a field.
- `determinant b` is the norm of the regular left multiplication. No reduced
  norm is defined or compared.
- Connectedness is proved for the fibres of the structure morphism over
  `Spec R`. No statement about a neutral component or a reductive quotient
  of a fibre is made.
