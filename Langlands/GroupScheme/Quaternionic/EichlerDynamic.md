# Eichler transformations are contracted by the hyperbolic cocharacter

Module `Langlands.GroupScheme.Quaternionic.EichlerDynamic`. The first two results are in
namespace `Langlands.GroupScheme.FiniteAlgebraUnits`. The rest are in
`Langlands.GroupScheme.Quaternionic.FirstKindInvolution.Eichler`.

## Setting

* `D` is a finite-dimensional division algebra over a field `K`, with an involution of the
  first kind `σ`. `q : σ.QuadraticForms n` is a `σ`-quadratic form on row vectors `D^n` with
  polar form `h(v, w) = σ.sesqForm (σ.polar q) v w`. Matrices act on row vectors, `v ↦ v M`.
* `O(q) = σ.isometryGroup q` is the Library's isometry group scheme.
  `ι = σ.isometryGroupι q` is its closed inclusion into the unit group scheme
  `FiniteAlgebraUnits.groupScheme b` of `M_n(D)`, with `b = Module.finBasis K (Matrix n n D)`.
* `h : σ.IsHyperbolicPair q e f` means `q(e) = 0`, `q(f) = 0` and `h(e, f) = 1`.
* For infinite `K`, `h.hyperbolicIsometryTorus : 𝔾_m ⟶ O(q)` is the Library's hyperbolic
  cocharacter (`HyperbolicTorus`). Its composite with `ι` is
  `h.hyperbolicUnitTorus = idempotentScalingHom P Q`. Here `P = σ.hyperbolicLineMatrix q e f`
  is the matrix of `v ↦ h(v, f) e` and `Q = σ.hyperbolicLineMatrix q f e` is the matrix of
  `v ↦ h(v, e) f`. So `t` scales `e` by `t` and `f` by `t⁻¹`, and fixes `{e, f}^⊥`.
* `formRankOne σ q y x` is the matrix of `v ↦ h(v, y) x`. `eichlerMatrix σ q f x c` is the
  Eichler transformation `E^f_{x,c} : v ↦ v + h(v,f) x - (h(v,x) + h(v,f) c) f`.
  `eichlerSet σ q f` is the set of units equal to some `E^f_{x,c}` with `h(x, f) = 0` and
  `[c] = q(x)` (module `EichlerTransformations`).

## Definitions

* `isometryRationalMatrix σ q : rationalPoints (σ.isometryGroup q) →* (Matrix n n D)ˣ`
  is the matrix of a rational point of `O(q)`. It sends `g` to
  `σ.isometryMatrixPoint q (rationalCoeffEquiv K _ g)`, the Library's matrix of the matching
  ground-field coefficient point (module `IsometryRowAction`). That matrix is computed through
  `ι` (`isometryRationalMatrix_apply`, by `rfl`), which makes the comparison with the
  hyperbolic cocharacter possible. The Library's `isometryGroupRationalPointsEquiv` (module
  `RationalIsometryPoints`) is a different construction, through the cut-out description of
  `O(q)`. This module does not prove that the two agree and does not use the older one.

## Results

* `FiniteAlgebraUnits.affinePointsEquiv_contractingPoint`: on the affine test scheme of a
  coefficient algebra `R`, the contracting point of `IsContracting p q N₁ N₂` (module
  `FiniteAlgebraIdempotentDynamic`) has unit `1 + N₁ + N₂` in `R ⊗[K] A`.
  `FiniteAlgebraUnits.lid_contractingUnit_one`: over `R = K` this unit is `1 + N₁ + N₂` in `A`.
* `isometryRationalMatrix_mem`: the matrix of a rational point lies in
  `rationalIsometryGroup σ q`.
* `isometryRationalMatrix_injective`: a rational point is determined by its matrix. The
  inclusion `ι` is a closed immersion, hence a monomorphism.
* `exists_isometryRationalMatrix_eq`: every element of `rationalIsometryGroup σ q` is the matrix
  of a rational point. The proof uses `map_lid_mem_rationalIsometryGroup_iff`
  (`RationalIsometryPoints`) and `IsHyperbolicPair.exists_isometryAffinePoint_of_defect`
  (`HyperbolicTorus`).
* `formRankOne_eq_hyperbolicLineMatrix`: `formRankOne σ q y x = σ.hyperbolicLineMatrix q x y`.
* `eichlerMatrix_eq_one_add`:
  `E^f_{x,c} = 1 + (formRankOne f x - formRankOne x f) + (-formRankOne f (c • f))`.
* **`isContracting_eichler`**: assume `h : σ.IsHyperbolicPair q e f` and `h(x, e) = h(x, f) = 0`.
  Let `N₁ = formRankOne f x - formRankOne x f`, the matrix of `v ↦ h(v,f) x - h(v,x) f`, and
  `N₂ = -formRankOne f (c • f)`, the matrix of `v ↦ -h(v,f) c f`. Then for every `c`,
  `IsContracting P Q N₁ N₂` holds. *Proof.* Each of the eight relations is checked on row
  vectors. It uses `h(e,e) = h(f,f) = 0`, `h(e,f) = h(f,e) = 1` and the orthogonality of `x`.
* `eichlerMatrix_eq_sub_smul`: let `β = h(x, e)`. Then for all `x` and `c`,
  `E^f_{x,c} = E^f_{x - β f, c + σ(β) - β}`.
  `sesqForm_sub_smul_left` gives `h(x - β f, e) = 0`. `sesqForm_sub_smul_right` gives
  `h(x - β f, f) = 0` when `h(x, f) = 0`.
* `rationalCoeffEquiv_symm_mem`: take a subgroup functor `F` of a group scheme `G` over
  `Spec K` and a `K`-coefficient point `z` in `F`. Then the rational point
  `(rationalCoeffEquiv K G).symm z` lies in `F`. It is `z` restricted along
  `ringTestSelfIso K`.
* **`exists_mem_unipotent_of_mem_eichlerSet`** (`[Infinite K]`, `[LinearOrder n]`): let
  `h : σ.IsHyperbolicPair q e f` and `u ∈ eichlerSet σ q f`. Then some rational point `g` of
  `O(q)` lies in `(Dynamic.unipotent h.hyperbolicIsometryTorus).carrier (Over.mk (𝟙 _))` and
  satisfies `isometryRationalMatrix σ q g = u`.
  *Proof.* `u` is a rational isometry (`eichlerSet_subset`), so it is the matrix of a rational
  point `g`. Write `u = E^f_{x,c}` and move `x` into `{e, f}^⊥` by
  `eichlerMatrix_eq_sub_smul`. Then `u = 1 + N₁ + N₂` with `IsContracting P Q N₁ N₂`. Let `z`
  be the coefficient point of `g`. Comparing units shows that `z ≫ ι` is the contracting point
  `1 + N₁ + N₂` of the unit group scheme. That point lies in the dynamic unipotent subgroup of
  `idempotentScalingHom P Q = h.hyperbolicIsometryTorus ≫ ι`
  (`contractingPoint_mem_unipotent`). Since `ι` is a closed subgroup,
  `Dynamic.unipotent_eq_comap_of_isClosedSubgroup` gives `z ∈ U(h.hyperbolicIsometryTorus)`.
  Then `rationalCoeffEquiv_symm_mem` gives `g`.
* `exists_mem_unipotent_of_mem_eichlerSet_left`: the same for `u ∈ eichlerSet σ q e`, with the
  opposite cocharacter `h.symm.hyperbolicIsometryTorus`. It scales `f` by `t` and `e` by `t⁻¹`.

## Provenance

Internal. The underlying fact is standard: the parts of an Eichler transformation along `f`
have weights `1` and `2` for the hyperbolic torus, so the torus contracts it to the identity.
See the dynamic description of `U(λ)` in Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
§2.1. The Lean proofs are direct computations with the Library's hyperbolic
cocharacter (Task 5397, `HyperbolicTorus`) and the contracting points of
`FiniteAlgebraIdempotentDynamic`. This module is a helper for Task 5398, where it is used to lift the Eichler
generators of the rational orthogonal group into the parabolic elementary subgroup of a spin
cover.
