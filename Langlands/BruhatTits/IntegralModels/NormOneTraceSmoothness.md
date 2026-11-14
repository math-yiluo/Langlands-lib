# A trace criterion for smoothness of norm-one tori

Let `A` be a commutative ring and `B` a finite free `A`-algebra. The
Library's norm-one group scheme `WeilGm.normOne A B` is the kernel of the
norm `R_{B/A} G_m → G_m` over `Spec A`. This module proves that it is smooth
over `Spec A` when `A` is noetherian and some element of `B` has trace one.

The Library already has a smoothness criterion for `normOne A B`,
`normOne_smooth_of_decomposition` in
`Langlands.BruhatTits.IntegralModels.NormOneTorusDepthZero`. It needs a
faithfully flat `A → A'` with `B ⊗ A' ≃ A'^I`, so it applies only when `B`
splits after such a base change. Such a splitting makes `B` étale over `A`,
so that criterion does not apply to the ring of integers of a ramified
quadratic extension of local fields. The trace criterion proved here does
not need a splitting. If `2` is a unit in `A` and
`B` has rank `2`, then `1/2` has trace one. So the criterion covers ramified
quadratic extensions in odd residue characteristic.

## Provenance

The module is derived. The argument is the standard first-order one: near
the identity, the norm of `1 + ε b` is `1 + ε Tr(b)`. So the differential of
the norm at the identity is the trace, and a trace-one element lets one
correct a lift to have norm one. The Lean proof is written here from
Mathlib and the Library; no external code is adapted.

The module prepares a regression unit for the task objective (Task 3557,
section "Regression examples"): the ramified quadratic norm-one torus. Its
comparison value is in Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`
(SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`),
read with the authors' corrections of 1 November 2024,
`kaletha-prasad-2024-corrections`
(SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`).

- The corrections replace Remark 2.5.15 (Section 2.5, PDF pp. 24–25). The
  corrected remark treats the kernel `T` of the norm map
  `R_{ℓ/k} G_m → G_m` for a separable quadratic extension `ℓ / k`. It shows
  that `T(k)_0` has index `2` in `T(k)` when `ℓ / k` is ramified. That
  regression needs a smooth integral model of `T`. The decomposition
  criterion does not give one, and this module does.
- KP §2.8 (printed pp. 110–112 / PDF pp. 141–143) studies the set
  `ℓ^{tr=1}` of trace-one elements of a separable quadratic extension
  `ℓ / k`. It notes that `1/2 ∈ ℓ^{tr=1}` when `p ≠ 2` (proof of
  Lemma 2.8.1). The hypothesis `HasTraceOne` is the corresponding condition
  for an algebra over a ring, and `hasTraceOne_of_isUnit_finrank` is the
  general form of the `1/2` remark. The corrections do not amend §2.8.

The Lean statements do not use KP's objects. They are stated for an
arbitrary finite free algebra over an arbitrary (for smoothness, noetherian)
base ring.

## Setting

The module imports the published
`Langlands.BruhatTits.IntegralModels.NormOneTorusDepthZero` (for `normOne`,
its points and the instance `normOne_isAffineHom`) and
`Langlands.GroupScheme.Torus.FixedSubgroupSmoothAlgebraBridge` (for
`smooth_of_coordinateAlgebra_smooth`). From Mathlib it imports
`Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff` (`Matrix.det_one_add_smul`),
`Mathlib.LinearAlgebra.TensorProduct.RightExactness`
(`Algebra.TensorProduct.lTensor_ker`) and `Mathlib.RingTheory.Nilpotent.Basic`.

It sets `backward.isDefEq.respectTransparency false` and opens
`CategoryTheory.MonObj` (scoped). All rings and algebras are in one
universe `u`. `tensorNorm A B S : B ⊗[A] S →* S` and its unit version
`tensorNormUnits` are the Library's determinant norms
(`Langlands.Algebra.TensorNorm`), with `S` as the coefficient ring.

## Declarations

### Namespace `Langlands.Algebra`

`A`, `B`, `S`, `S'` are commutative rings, with `B`, `S`, `S'` algebras
over `A`.

- `HasTraceOne A B` (definition, the declared definition of this unit): the
  proposition `∃ b : B, Algebra.trace A B b = 1`.
- `hasTraceOne_iff_surjective`: `HasTraceOne A B` holds exactly when
  `Algebra.trace A B : B → A` is surjective.
- `hasTraceOne_of_isUnit_finrank`: if `A` is nontrivial, `B` is finite free
  over `A`, and `Module.finrank A B` is a unit in `A`, then
  `HasTraceOne A B`. The element is the image in `B` of the inverse rank.
- `tensorNorm_one_add_tmul` (`B` finite free): for `b : B` and `r : S` with
  `r ^ 2 = 0`,
  `tensorNorm A B S (1 + b ⊗ₜ r) = 1 + r * algebraMap A S (Algebra.trace A B b)`.
- `lTensor_mul_eq_zero`: let `φ : S →ₐ[A] S'` be surjective with
  `RingHom.ker φ ^ 2 = ⊥`. If `x y : B ⊗[A] S` are both killed by
  `Algebra.TensorProduct.lTensor B φ`, then `x * y = 0`.
- `exists_tensorNormUnits_lift` (square-zero lifting; `B` finite free): let
  `HasTraceOne A B` hold, and let `φ : S →ₐ[A] S'` be surjective with
  `RingHom.ker φ ^ 2 = ⊥`. Then every `u'` in the kernel of
  `tensorNormUnits A B S'` is the image, under the unit map of
  `lTensor B φ`, of some `u` in the kernel of `tensorNormUnits A B S`.

### Namespace `Langlands.GroupScheme.WeilGm`

`A` is a `CommRingCat.{u}`.

- `specSectionsIso A C` (definition, for `C : CommAlgCat A`): the
  isomorphism `C ≅ ((algΓ A).obj ((algSpec A).obj (op C))).unop`. It is the
  counit of Mathlib's adjunction `algΓAlgSpecAdjunction A` at `op C`, which
  is an isomorphism (`asIso`), taken through `unop`.
- `specSectionsIso_naturality`: for `g : C ⟶ D` in `CommAlgCat A`,
  `(specSectionsIso A C).hom ≫ ((algΓ A).map ((algSpec A).map g.op)).unop =
  g ≫ (specSectionsIso A D).hom`.

For the remaining items `B` is finite free over `A`.

- `normOne_locallyOfFiniteType` (instance):
  `LocallyOfFiniteType (normOne A B).X.hom`. The inclusion of the kernel is
  a closed immersion into the smooth group scheme `groupScheme A B`.
- `normOne_formallySmooth_of_hasTraceOne`: if `HasTraceOne A B`, then
  `Algebra.FormallySmooth A (Lie.coordinateAlgebra (normOne A B))`.
- `normOne_smooth_of_hasTraceOne` (headline result): if `A` is noetherian
  and `HasTraceOne A B`, then `Smooth (normOne A B).X.hom`.

## Proof outline

**First-order norm formula.** Choose a basis `β` of `B` over `A`. The
commutativity isomorphism takes `1 + b ⊗ r` to `1 + r • (1 ⊗ b)` in
`S ⊗[A] B`. In the base-changed basis the multiplication matrix of `1 ⊗ b`
is the image of that of `b`, entry by entry. Mathlib's
`Matrix.det_one_add_smul` writes `det (1 + r • M)` as `1 + trace M * r`
plus a multiple of `r ^ 2`, which is zero. The trace of the image matrix is the
image of the trace (`AddMonoidHom.map_trace`), and
`Algebra.trace_eq_matrix_trace` identifies it with `Tr(b)`.

**Square-zero kernel after tensoring.** By Mathlib's
`Algebra.TensorProduct.lTensor_ker`, the kernel of `id_B ⊗ φ` is the
extension of `ker φ`. The extension of a square-zero ideal has square zero
(`Ideal.map_pow`). The Library lemma
`CommutativeAlgebra.GradedFormallySmooth.mul_eq_zero_of_sq_eq_bot` then
gives `x * y = 0`.

**Lifting.** The map `Ψ = id_B ⊗ φ` is surjective. Lift `u'` and its
inverse to `z₀` and `w₀`. Then `z₀ w₀ - 1` lies in the kernel of `Ψ`, so it
squares to zero; hence `z₀ w₀` is a unit (`IsNilpotent.isUnit_add_one`), and
so is `z₀`. Put `k = N(z₀) - 1`. Naturality of the norm
(`tensorNorm_naturality`) gives `φ k = N(u') - 1 = 0`, so `k ∈ ker φ` and
`k ^ 2 = 0`. Let `b₀` have trace one and put `c₀ = 1 + b₀ ⊗ (-k)`. By the
first-order formula `N(c₀) = 1 - k`. Also `Ψ c₀ = 1`, so `c₀` is a unit.
The unit `u = z₀ c₀` has norm `(1 + k)(1 - k) = 1 - k ^ 2 = 1` and maps to
`u'`.

**Formal smoothness.** The proof uses
`Algebra.FormallySmooth.of_comp_surjective`. Let `C` be an `A`-algebra with
an ideal `I` such that `I ^ 2 = ⊥`, and let
`f : coordinateAlgebra →ₐ[A] C ⧸ I`. The inverse of the Library's
`Lie.pointCoordinates` turns `f` into a morphism
`Spec (C ⧸ I) ⟶ (normOne A B).X` (an element of `Lie.AffinePoints`).
`normOnePointsEquiv` turns that point into a norm-one unit `u₀` of
`B ⊗ Γ(Spec (C ⧸ I))`. The map `φ` on global sections induced by
`C → C ⧸ I` corresponds to the quotient map under `specSectionsIso`. So `φ`
is surjective with square-zero kernel, and the lifting lemma gives a
norm-one unit `u₁` over `Spec C` lifting `u₀`. By
`normOnePointsEquiv_naturality`, the point `x₁` corresponding to `u₁`
restricts to the given point. By `Lie.pointCoordinates_naturality`,
`Lie.pointCoordinates` applied to `x₁` is the required lift: an `A`-algebra
map from the coordinate algebra to `C` whose composite with `C → C ⧸ I` is
`f`.

**Smoothness.** For noetherian `A`, the coordinate algebra is of finite type
(`Lie.coordinateAlgebraFiniteType`, using the instance above), hence of
finite presentation. Together with formal smoothness it is smooth over `A`.
The Library's `smooth_of_coordinateAlgebra_smooth` (with the published
`normOne_isAffineHom`) gives smoothness of `(normOne A B).X.hom`.

## Non-claims

- No claim is made without the trace-one hypothesis, or without the
  noetherian hypothesis in `normOne_smooth_of_hasTraceOne`. The formal
  smoothness statement needs no noetherian hypothesis.
- The module does not identify `normOne A B` with a Néron model, a
  connected Néron model, or any parahoric or Bruhat–Tits group scheme. It
  does not compute `T(k)_0`, KP's `μ`, or any index.
- The ramified quadratic regression described under Provenance is not part
  of this module.
