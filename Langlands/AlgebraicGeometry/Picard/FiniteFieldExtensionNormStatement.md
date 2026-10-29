# Norms of functions along a finite field-extension base change

`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNormStatement.{u}` is
a universe-polymorphic `Prop`-valued definition. It is a statement target:
this module supplies no proof and adds no axiom.

Worker 770 wrote the Lean statement and a first companion draft, and specified
the task. Worker 712 checked the statement against the source and expanded
this companion.

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
and `d` for `Module.finrank K L`. The proposition asserts that there exists

```text
Nm : ∀ U : X.Opens, Γ(X_L, π ⁻¹ᵁ U) →* Γ(X, U)
```

such that the following three clauses hold.

1. **Restriction.** For all opens `U ≤ V` of `X` and every
   `f : Γ(X_L, π ⁻¹ᵁ V)`,

   ```text
   X.presheaf.map (homOfLE hUV).op (Nm V f) =
     Nm U (X_L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π hUV)).op f)
   ```

   Restricting the norm from `V` to `U` gives the norm of the restriction
   from `π⁻¹ V` to `π⁻¹ U`. `Scheme.Hom.preimage_mono π hUV` is the
   inclusion `π⁻¹ U ≤ π⁻¹ V`.
2. **Degree.** For every open `U` of `X` and every `g : Γ(X, U)`,
   `Nm U (π.app U g) = g ^ d`, where `π.app U : Γ(X, U) ⟶ Γ(X_L, π⁻¹ U)` is
   the pullback of functions along `π`.
3. **Nonvanishing locus.** For every open `U` of `X` and every
   `f : Γ(X_L, π ⁻¹ᵁ U)`, the following two sets of points of `X` are equal:

   ```text
   (X.basicOpen (Nm U f) : Set X) =
     {x : X | x ∈ U ∧ ∀ y : X_L, π.base y = x → y ∈ X_L.basicOpen f}
   ```

   Here `y` ranges over all points of `X_L`. In the Lean text the binder is
   written `∀ y : (pullback p … : Scheme.{u})`; the type ascription makes
   `pullback` the pullback in `Scheme.{u}`.

`Γ(Y, W)` is the ring of sections of the structure sheaf of `Y` over the open
`W`, and `π ⁻¹ᵁ U` is the preimage open. For a section `f : Γ(Y, W)`,
Mathlib's `Y.basicOpen f` is the set of points `y ∈ W` at which the germ of
`f` is a unit. Mathlib's `Scheme.evaluation_eq_zero_iff_notMem_basicOpen`
shows that this is the set of points where the value of `f` in the residue
field is nonzero, that is, the nonvanishing locus of `f`. So clause 3 says:
`Nm U f` is nonvanishing at `x` exactly when `x ∈ U` and `f` is nonvanishing
at every point of the fibre `π⁻¹(x)`.

`Nm U` has type `→*` (a monoid homomorphism), so it is multiplicative and
sends `1` to `1`. The equality `Nm U 1 = 1` also follows from clause 2 with
`g = 1`, so the bundled form asks for nothing beyond a multiplicative map
satisfying clause 2. A monoid homomorphism sends units to units. Additivity
is not asserted.

The statement asserts only that such a family exists. It does not assert
that `Nm` is unique or canonical, that it equals a determinant, or that its
formation commutes with base change. The norm and its properties are not
supplied as data or premises: the proposition is a plain existential over
the given `K`, `L`, `X` and `p`.

## Scope

All universes `u` and all fields `K` of any characteristic are included,
with `L / K` any finite extension: separable, inseparable and the trivial
extension `L = K` (then `d = 1`). The pair `(X, p)` is arbitrary: `X` may be
empty, non-affine, non-separated, non-quasi-compact, non-reduced or
non-noetherian, and need not be of finite type over `K`. The clauses are
required for every open `U` of `X`, not only affine opens. There is no
separability, chosen basis or chosen affine cover premise. The degree is
exactly `Module.finrank K L`, the `K`-dimension of `L` for the module
structure induced by the algebra structure. It is at least `1` because `L`
is a nonzero finite-dimensional `K`-vector space.

## Source correspondence and derived provenance

The source is Stacks Project Section 31.18 "Norms" (tag 0BCX). This
proposition specializes its notion of a norm of degree `d` to the projection
`π : X_L → X` of a finite field-extension base change. Clause 3 is a derived
formulation, explained below.

**The definition.** At the start of Section 31.18, for a finite morphism
`π : X → Y` and an integer `d ≥ 1`, a norm of degree `d` for `π` is a
multiplicative map of sheaves `Norm_π : π_* 𝒪_X → 𝒪_Y` such that

- (1) the composition `𝒪_Y → π_* 𝒪_X → 𝒪_Y` of `π^♯` and `Norm_π` equals
  `g ↦ g^d`, and
- (2) for `V ⊂ Y` open, if `f ∈ 𝒪_X(π⁻¹ V)` is zero at `x ∈ π⁻¹(V)`, then
  `Norm_π(f)` is zero at `π(x)`.

Here the source's `X → Y` is our `X_L → X`. The source's `Y` and its opens
`V` are our `X` and its opens `U`.

- `Nm U` is the norm on `(π_* 𝒪_{X_L})(U) = Γ(X_L, π⁻¹ U)` with values in
  `Γ(X, U)`. The `→*` type is "multiplicative", and clause 1 says that the
  family `Nm` commutes with restriction, so it is a morphism of sheaves (of
  multiplicative monoids) `π_* 𝒪_{X_L} → 𝒪_X`.
- Clause 2 is condition (1): `Norm ∘ π^♯ = (g ↦ g^d)` on every open.
- Clause 3 combines condition (2) with the remark that follows the
  definition, as explained next.

**The units remark.** After the definition the source observes:
"Since `Norm_π` is multiplicative it sends units to units hence, given
`y ∈ Y`, if `f` is a regular function on `X` defined at but nonvanishing at
any `x ∈ X` with `π(x) = y`, then `Norm_π(f)` is defined and does not vanish
at `y`." Here "nonvanishing at any `x`" means nonvanishing at every point
`x` of the fibre over `y`. The source notes that this holds without condition
(2).

**Clause 3, inclusion `⊆`.** Let `x ∈ X.basicOpen (Nm U f)`. Then `x ∈ U`.
If `f` vanished at some point `y` with `π y = x`, condition (2) with
`V := U` would make `Nm U f` vanish at `x`. So `f` is nonvanishing at every
point of the fibre. This inclusion is the contrapositive of condition (2).

**Clause 3, inclusion `⊇`.** This is the units remark. Let `x ∈ U` with
`f` nonvanishing at every point of `π⁻¹(x)`. The restriction
`π⁻¹ U → U` is finite, hence closed. The complement `Z` of
`X_L.basicOpen f` in `π⁻¹ U` is closed, so `U \ π(Z)` is an open
neighbourhood `W` of `x` with `π⁻¹ W ⊂ X_L.basicOpen f`. The restriction of
`f` to `π⁻¹ W` is a unit. By multiplicativity its norm is a unit of
`Γ(X, W)`, and by clause 1 that norm is the restriction of `Nm U f` to `W`.
So `x ∈ X.basicOpen (Nm U f)`. The source does not spell out this
shrinking step.

**Clause 3 from Lemma 31.18.6.** Both inclusions can also be read off the
norm of Lemma 31.18.6, using its compatibility with base change. That lemma
says that a finite locally free morphism of degree `d ≥ 1` has a canonical
norm of degree `d` whose formation commutes with arbitrary base change. On
an affine open `V` over which `π_* 𝒪_X` is free of rank `d`, the norm of `f`
is `det(M_f)`, the determinant of multiplication by `f` in a basis. To prove
condition (2), the source base changes to the spectrum of a field `k`, where
`X = Spec(A)` with `dim_k A = d`. Then, for our `π` and a point `x ∈ U`, the
value of the norm at `x` is the determinant of multiplication by `f` on the
`d`-dimensional `κ(x)`-algebra `A_x = κ(x) ⊗_K L`. The points of the fibre
`π⁻¹(x)` are the prime ideals of `A_x`. This determinant is nonzero exactly
when multiplication by `f` is bijective, that is, when the image of `f` is a
unit of `A_x`. Since `A_x` is finite-dimensional over a field, that holds
exactly when the image of `f` lies in no prime ideal of `A_x`, that is, when
`f` is nonvanishing on the whole fibre. The source's proof of (2) gives the
direction "vanishing at a point of the fibre implies `det = 0`". The
converse is the determinant criterion for invertibility.

So the equality of clause 3 is a derived, slightly sharper formulation than
the displayed source condition. It follows from condition (2) together with
the units remark, and also from Lemma 31.18.6 with its base-change
compatibility. The source does not display this equality.

**Applicability of Lemma 31.18.6.** The morphism `π` is the base change
along `p` of `Spec L → Spec K`. That morphism is finite free of rank `d`, so
`π` is finite locally free of constant degree `d ≥ 1`. Concretely, over an
affine open `Spec A` of `X` the preimage is `Spec (A ⊗[K] L)`, and
`A ⊗[K] L` is a free `A`-module of rank `d`, with a basis coming from a
`K`-basis of `L`. These are facts about the setting that a proof must
establish; they are not premises of the proposition. The source also
observes that condition (1) forces `π` to be surjective. The proposition does
not state surjectivity.

## Original source and reading record

Registered source `stacks-norms-field-ample-descent-2026-10-26`, directory
SHA256 `af3256169e1d1a032cecd20fa228482bad8e1b478ccfc55a4a73c7ec187d9f5a`,
retained at
`literature/Stacks Project - Norms and field-extension ampleness descent (HTML snapshot 2026-10-26)/0BCX.html`.
On October 28, 2026 Worker 712 reread from the retained Section 31.18: the
definition of a norm of degree `d`, the remark after it, Lemmas
31.18.1–31.18.8, Proposition 31.18.9 and Lemma 31.18.10 with their proofs,
and the section's two comments.
Comment #7175 (April 2022) asks whether the `V` in item (2) was already
defined. Comment #7312 replies that this was fixed, and the retained
definition declares `V ⊂ Y` open. The footnote after "norm of degree `d` for
`π`" only says the phrase is nonstandard notation. No other erratum affects
the parts used here, and the Library at the working base has no erratum file
for this source.

## Obligations for a future proof

A proof of the exact proposition, with no additional outer hypothesis, must
construct `Nm` on every open of `X`, not only affine opens. One route: over
an affine open `Spec A` of `X` identify the preimage with
`Spec (A ⊗[K] L)` (Mathlib `pullbackSpecIso`) and take Mathlib's
`Algebra.norm A` on the free `A`-algebra `A ⊗[K] L`; check compatibility
with localization; glue to all opens using the sheaf property; obtain clause
2 from `Algebra.norm_algebraMap`; and prove clause 3 from the unit criterion
for elements of a finite-dimensional algebra over a field, together with the
description of the fibre. This module discharges none of these obligations.
