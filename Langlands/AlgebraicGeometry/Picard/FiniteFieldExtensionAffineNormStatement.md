# Compatible norms on affine opens along a finite field-extension base change

`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionAffineNormStatement.{u}`
is a universe-polymorphic `Prop`-valued definition. It is a statement target:
this module supplies no proof and adds no axiom.

Worker 1020 wrote the Lean statement and this companion. Worker 208 specified
the task.

This proposition is the affine-open counterpart of the published target
`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNormStatement`. It is a
separate declaration in a separate module and does not modify that target, its
Lean file or its Markdown file. It does not import that target.

## Exact statement

The module imports only Mathlib (`Mathlib.AlgebraicGeometry.Pullbacks`,
`Mathlib.LinearAlgebra.Dimension.Finrank`,
`Mathlib.LinearAlgebra.FiniteDimensional.Defs`) and opens
`CategoryTheory`, `CategoryTheory.Limits` and `AlgebraicGeometry`.

The proposition quantifies over:

- fields `K L : Type u` with `[Algebra K L]` and `[FiniteDimensional K L]`;
- a scheme `X : Scheme.{u}`;
- a morphism `p : X ⟶ Spec (CommRingCat.of K)`.

Write `X_L` for the actual Mathlib pullback
`pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L)))` in `Scheme.{u}`.
This is the base change `X ×_{Spec K} Spec L` of the `K`-scheme `(X, p)`.
Write `π` for its first projection
`pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L))) : X_L ⟶ X`,
and `d` for `Module.finrank K L`. The Lean text writes out these pullback
terms in full; `X_L`, `π` and `d` are only abbreviations in this companion.

`X.affineOpens` is Mathlib's set `Scheme.affineOpens X` of opens `U` of `X`
such that the open subscheme on `U` is affine (`IsAffineOpen U`). An element
`U : X.affineOpens` is such an open together with that proof, and
`(U : X.Opens)` is the underlying open.

The proposition asserts that there exists

```text
Nm : ∀ U : X.affineOpens, Γ(X_L, π ⁻¹ᵁ (U : X.Opens)) →* Γ(X, (U : X.Opens))
```

such that the following three clauses hold.

1. **Restriction along affine inclusions.** For all affine opens `U`, `V`
   of `X`, every proof `hUV : (U : X.Opens) ≤ (V : X.Opens)` and every
   `f : Γ(X_L, π ⁻¹ᵁ (V : X.Opens))`,

   ```text
   X.presheaf.map (homOfLE hUV).op (Nm V f) =
     Nm U (X_L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π hUV)).op f)
   ```

   Restricting the norm from `V` to `U` gives the norm of the restriction
   from `π⁻¹ V` to `π⁻¹ U`. `Scheme.Hom.preimage_mono π hUV` is the
   inclusion `π⁻¹ U ≤ π⁻¹ V`.
2. **Degree.** For every affine open `U` and every `g : Γ(X, (U : X.Opens))`,
   `Nm U (π.app (U : X.Opens) g) = g ^ d`, where `π.app (U : X.Opens)` is the
   pullback of functions `Γ(X, U) ⟶ Γ(X_L, π⁻¹ U)` along `π`.
3. **Nonvanishing locus.** For every affine open `U` and every
   `f : Γ(X_L, π ⁻¹ᵁ (U : X.Opens))`, the following two sets of points of
   `X` are equal:

   ```text
   (X.basicOpen (Nm U f) : Set X) =
     {x : X | x ∈ (U : X.Opens) ∧ ∀ y : X_L, π.base y = x → y ∈ X_L.basicOpen f}
   ```

   Here `y` ranges over all points of `X_L`. In the Lean text the binder is
   written `∀ y : (pullback p … : Scheme.{u})`; the type ascription makes
   `pullback` the pullback in `Scheme.{u}`.

`Γ(Y, W)` is the ring of sections of the structure sheaf of `Y` over the open
`W`, and `π ⁻¹ᵁ U` is the preimage open. For a section `f : Γ(Y, W)`,
Mathlib's `Y.basicOpen f` is the set of points `y ∈ W` at which the germ of
`f` is a unit. Mathlib's `Scheme.evaluation_eq_zero_iff_notMem_basicOpen`
shows that this is the set of points of `W` where the value of `f` in the
residue field is nonzero, that is, the nonvanishing locus of `f`. So clause 3
says: `Nm U f` is nonvanishing at `x` exactly when `x ∈ U` and `f` is
nonvanishing at every point of the fibre `π⁻¹(x)`. The clause is a two-sided
equality of sets, not only the implication "vanishing somewhere on the fibre
implies vanishing of the norm".

Each `Nm U` has type `→*` (a monoid homomorphism), so it is multiplicative
and sends `1` to `1`. A monoid homomorphism sends units to units. Additivity
is not asserted.

The statement asserts only that such a family exists, with all three laws as
conclusions. The family `Nm` and its laws are not supplied as data or
premises: the proposition is a plain existential over the given `K`, `L`, `X`
and `p`. It does not assert that `Nm` is unique or canonical, that it equals
a determinant (Mathlib's `Algebra.norm`), or that its formation commutes with
base change.

## Scope

All universes `u` and all fields `K` of any characteristic are included,
with `L / K` any finite extension: separable, inseparable and the trivial
extension `L = K` (then `d = 1`). The degree is exactly
`Module.finrank K L`, the `K`-dimension of `L` for the module structure
induced by the algebra structure; it is at least `1`. The pair `(X, p)` is
arbitrary: `X` may be empty, non-affine, non-separated, non-quasi-compact,
non-reduced or non-noetherian, and need not be of finite type over `K`.
There is no separability, chosen basis or chosen affine cover premise.

The family is indexed by *all* affine opens of `X`, and clause 1 is required
for *every* inclusion `U ≤ V` of affine opens. No condition is placed on
intersections: when two affine opens have a non-affine intersection (which can
happen when `X` is not separated), clause 1 still applies to every affine open
contained in both. Clauses 2 and 3 are required on every affine open.

The difference from `FiniteFieldExtensionNormStatement` is only the index set:
that target asks for `Nm U` and the three laws on every open `U` of `X`, this
one on every affine open. The three clauses have the same form, with
`U : X.Opens` replaced by `(U : X.affineOpens)` coerced to `X.Opens`. Restricting
a family satisfying the parent target to the affine opens gives a family
satisfying this proposition. Conversely, the accepted Library construction
`Langlands.AlgebraicGeometry.Picard.AffineNormGluing.norm` (module
`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNormGluing`) extends a
family on all affine opens to all opens. The hypotheses `N`, `hN` of that
construction and the hypotheses `hd` of its lemma `degree` (with
`d := Module.finrank K L`) and `hB` of its lemma `basicOpen`, for
`π := pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L)))`, have the
forms of `Nm` and clauses 1, 2 and 3 here, and its lemmas `naturality`,
`degree` and `basicOpen` give the three clauses of the parent target. This
module proves neither implication. The author checked both by a private
development compilation that is not part of this submission; the
affine-to-all-open step belongs to the parent proof task
`f78fa110-e7ad-4e40-bbd9-afd15533f4e5`.

## Source correspondence and derived provenance

The source is Stacks Project Section 31.18 "Norms" (tag 0BCX). This
proposition is an internal, derived affine-local specialization of the notion
of a norm of degree `d` to the projection `π : X_L → X` of a finite
field-extension base change. It is not a verbatim source statement.

**The definition.** At the start of Section 31.18, for a finite morphism
`π : X → Y` and an integer `d ≥ 1`, a norm of degree `d` for `π` is a
multiplicative map of sheaves `Norm_π : π_* 𝒪_X → 𝒪_Y` such that

- (1) the composition `𝒪_Y → π_* 𝒪_X → 𝒪_Y` of `π^♯` and `Norm_π` equals
  `g ↦ g^d`, and
- (2) for `V ⊂ Y` open, if `f ∈ 𝒪_X(π⁻¹ V)` is zero at `x ∈ π⁻¹(V)`, then
  `Norm_π(f)` is zero at `π(x)`.

Here the source's `X → Y` is our `X_L → X`, and the source's opens `V ⊂ Y`
are our opens of `X`.

**Affine-local provenance.** The affine opens of a scheme form a basis of its
topology (Mathlib `Scheme.isBasis_affineOpens`). A morphism of sheaves is
determined by its values on the opens of a basis, and a family of maps on the
basis opens that commutes with restriction along every inclusion of basis
opens extends uniquely to a morphism of sheaves. The proposition records the
source's norm on the basis of affine opens:

- `Nm U` is the norm on `(π_* 𝒪_{X_L})(U) = Γ(X_L, π⁻¹ U)` for an affine
  open `U`, with values in `Γ(X, U)`. The `→*` type is "multiplicative".
- Clause 1 is the commutation with restriction along inclusions of affine
  opens, that is, the morphism-of-sheaves condition restricted to the basis.
- Clause 2 is condition (1) on affine opens.
- Clause 3 combines condition (2) with the remark that follows the definition,
  on affine opens, as explained below.

Lemma 31.18.6 also works affine-locally: on an affine open over which
`π_* 𝒪_X` is finite free it defines the norm as a determinant and says that
the local definitions glue. In our setting `π` is finite locally free of
degree `d`, and every affine open qualifies (see the obligations below).

**The units remark.** After the definition the source observes:
"Since `Norm_π` is multiplicative it sends units to units hence, given
`y ∈ Y`, if `f` is a regular function on `X` defined at but nonvanishing at
any `x ∈ X` with `π(x) = y`, then `Norm_π(f)` is defined and does not vanish
at `y`." Here "nonvanishing at any `x`" means nonvanishing at every point of
the fibre over `y`.

**Clause 3, inclusion `⊆`.** If `x` lies in the basic open of `Nm U f`, then
`x ∈ U`, and if `f` vanished at some `y` with `π y = x`, condition (2) would
make `Nm U f` vanish at `x`. So this inclusion is the contrapositive of
condition (2) for the affine open `U`.

**Clause 3, inclusion `⊇`.** This is the units remark. If `x ∈ U` and `f` is
nonvanishing on all of `π⁻¹(x)`, then, since `π` is finite and hence closed,
there is an open neighbourhood `W ⊂ U` of `x` with `π⁻¹ W` inside the basic
open of `f`; the norm of the unit `f|_{π⁻¹ W}` is a unit and is the
restriction of `Nm U f`. Here `W` may be chosen affine (a basic open of `U`),
so this argument uses only clause 1 for affine opens. The source does not
spell out this shrinking step.

**Clause 3 from Lemma 31.18.6.** Both inclusions can also be read off the
determinant norm of Lemma 31.18.6 and its base-change compatibility. For a
point `x ∈ U`, the value of the norm at `x` is the determinant of
multiplication by `f` on the `d`-dimensional `κ(x)`-algebra `κ(x) ⊗_K L`,
whose prime ideals are the points of `π⁻¹(x)`. It is nonzero exactly when
the image of `f` is a unit of that algebra, that is, lies in no prime ideal.
The source's proof of (2) gives the direction "vanishing at a point of the
fibre implies `det = 0`"; the converse is the determinant criterion for
invertibility.

So clause 3 is a derived, slightly sharper two-sided formulation than the
displayed source condition. The source does not display this equality. The
published companion `FiniteFieldExtensionNormStatement.md` gives the same
derivation for all opens.

## Original source and reading record

Registered source `stacks-norms-field-ample-descent-2026-10-26`, directory
SHA256 `af3256169e1d1a032cecd20fa228482bad8e1b478ccfc55a4a73c7ec187d9f5a`,
retained at
`literature/Stacks Project - Norms and field-extension ampleness descent (HTML snapshot 2026-10-26)/0BCX.html`.
On October 29, 2026 Worker 1020 read from the retained Section 31.18: the
definition of a norm of degree `d`, the remark after it, and Lemma 31.18.6
with its proof. Worker 1020 also read the complete published companion
`Langlands/AlgebraicGeometry/Picard/FiniteFieldExtensionNormStatement.md`,
including its erratum check for this source.

## Obligations for a future proof

A proof of the exact proposition, with no additional outer hypothesis, must
construct `Nm U` for every affine open `U` of `X` and prove the three clauses
for all affine opens and all affine inclusions. This module discharges none
of these obligations. One route:

- For an affine open `U` with `A := Γ(X, U)`, identify `π⁻¹ U` with
  `Spec (A ⊗[K] L)`, for example with Mathlib's `pullbackSpecIso`,
  `IsAffineOpen.isoSpec` and `IsAffineOpen.fromSpec`, and the sections
  `Γ(X_L, π⁻¹ U)` with `A ⊗[K] L` compatibly with `π.app`.
- Define `Nm U` from Mathlib's determinant norm `Algebra.norm A` on the
  free `A`-algebra `A ⊗[K] L` of rank `d` (a basis comes from a `K`-basis of
  `L`, for example via `Algebra.TensorProduct.basis`).
- Clause 1: for affine `U ≤ V`, the restriction `Γ(X, V) → Γ(X, U)` and the
  restriction on preimages correspond, under the identifications
  (`IsAffineOpen.map_fromSpec`), to the ring map `B → A` and its base change
  `B ⊗[K] L → A ⊗[K] L`. The required identity is the compatibility of
  `Algebra.norm` with base change of a free algebra. The intersection of two
  affine opens is never used.
- Clause 2: `Algebra.norm_algebraMap`, using
  `Module.finrank A (A ⊗[K] L) = Module.finrank K L` when `A` is nonzero.
  When `U` is empty, `A` is the zero ring and every equation in `A` holds.
- Clause 3: for a point `x ∈ U`, compare the value of `Algebra.norm A f` in
  the residue field `κ(x)` with the norm of the image of `f` in the
  finite-dimensional `κ(x)`-algebra `κ(x) ⊗[K] L`, identify the points of
  the fibre `π⁻¹(x)` with the prime ideals of that algebra, and use the
  criterion that an element of a finite-dimensional algebra over a field has
  nonzero norm if and only if it is a unit, if and only if it lies in no
  prime ideal. Both inclusions are required.

Substantial canonical affine-comparison definitions may be split into a
separate focused definition task, and the algebraic laws for
`Algebra.norm A` on `A ⊗[K] L` may come from a separate published algebraic
statement and proof. An unproved comparison must not be added as an outer
hypothesis.
