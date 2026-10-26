# Polynomial modules and modules with an endomorphism

The namespace `Langlands.Algebra.PolynomialEndomorphism` constructs an actual
equivalence of categories

```lean
equivalence.{u, v} (R : Type u) [CommRing R] :
  ModuleCat.{v} R[X] ≌ EndomorphismCat.{u, v} R

fieldEquivalence.{u, v} (k : Type u) [Field k] :
  ModuleCat.{v} k[X] ≌ EndomorphismCat.{u, v} k
```

The equivalence has explicit object and morphism maps, natural unit and counit
isomorphisms, and the coherence field required by `CategoryTheory.Equivalence`.
Every module is a unital left module. There are no hypotheses on module
dimension, finite generation, field characteristic, or algebraic closure.

## Original source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, Appendix A.III.1, example 5, printed page 252 / PDF page 258,
first assertion before localization at the powers of `X`.

- Registered literature ID:
  `renard-2026-representations-groupes-reductifs-padiques`.
- Source file:
  `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
- SHA256:
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The source identifies the category of unital left `k[X]`-modules with the
category whose objects are pairs consisting of a `k`-vector space and a linear
endomorphism, and whose morphisms are linear intertwiners. The declaration
`fieldEquivalence` implements exactly that assertion for every field.
The construction over an arbitrary commutative ring, the chosen categorical
encoding, and the explicit comparison formulas are derived implementation
content; the book is not being cited as stating this ring generalization or
these Lean declarations. Worker 490 implemented the construction; Worker 6
contributed the original-source audit, scope, and Mathlib reuse route.

## Category and composition convention

`EndomorphismCat.{u, v} R` abbreviates
`CategoryTheory.Endofunctor.Algebra (𝟭 (ModuleCat.{v} R))`. An object `A` consists
of an actual module `A.a` and a structure morphism `A.str : A.a ⟶ A.a`.
This is an algebra for an endofunctor, with no monad algebra laws imposed.
Consequently `A.str` is an arbitrary linear endomorphism.
`endomorphism R A` exposes its linear map as `Module.End R A.a`.

A morphism `f : A ⟶ B` has an underlying module morphism `f.f` and equation

```lean
((𝟭 (ModuleCat R)).map f.f) ≫ B.str = A.str ≫ f.f
```

Lean's diagrammatic composition makes the left side the function
`x ↦ B.str (f.f x)`, and the right side `x ↦ f.f (A.str x)`.
`intertwining_iff` proves that this equation is equivalent to
`∀ x, f.f (A.str x) = B.str (f.f x)`: one direction evaluates the equality
and takes its symmetry, and the other uses extensionality.
`homEquiv` gives the exact bijection between categorical morphisms and

```lean
{f : A.a →ₗ[R] B.a // ∀ x, f (A.str x) = B.str (f x)}
```

by retaining the same linear map and translating this equation in both
directions. Its inverse identities are definitional.

## The two functors

Write `F = fromPolynomial R` and `G = toPolynomial R`.

`restrict R` is Mathlib's `ModuleCat.restrictScalars Polynomial.C`. For a
polynomial module `M`, its underlying additive group is unchanged and its
`R`-action is `r • m = Polynomial.C r • m`, recorded by `restrict_smul`.
`xAction R M` is the `R`-linear morphism on this restricted module with value
`X • m`, as exposed by `xAction_apply`. Linearity follows from distributivity
and commuting polynomial scalar actions.

`F.obj M` is the restricted module with this actual `X`-action. `F.map f`
restricts the original polynomial-linear map `f`; its intertwining equation is
the symmetry of `f.hom.map_smul X`. The formula `fromPolynomial_map_apply`
states that the underlying function is still `f`.
The functor's identity and composition fields are proved by extensionality and
definitional equality.

For `A` in `EndomorphismCat R`, put `a = endomorphism R A` and let
`eₐ = Module.AEval'.of a` denote Mathlib's carrier identification.
`toPolynomialObj R A` is `ModuleCat.of R[X] (Module.AEval' a)`.
Thus its polynomial action is evaluation at the given endomorphism:

```text
p • eₐ(x) = eₐ((aeval a p) x).
```

`toPolynomial_smul` exposes this defining formula.
`toPolynomial_C_smul` states
`C r • eₐ(x) = eₐ(r • x)`, using `Module.AEval.C_smul` and the linearity of
`eₐ`. `toPolynomial_X_smul` states
`X • eₐ(x) = eₐ(A.str x)`, using `Module.AEval'.X_smul_of`.
In particular the construction recovers both constant scalar multiplication
and the specified endomorphism.

`toPolynomialMap` uses `LinearMap.ofAEval` to make each intertwiner
polynomial-linear. Its compatibility premise is obtained from
`intertwining_iff` and the formula for the action of `X`.
`toPolynomialMap_of` states the underlying map formula

```text
G.map f (eₐ(x)) = e_b(f.f x).
```

`toPolynomial` packages these object and morphism constructions into `G`.
Again identity and composition follow by extensionality and definitional
equality.

## Round trips, naturality, and coherence

`polynomialRoundTrip R M : G.obj (F.obj M) ≅ M` is built with
`LinearEquiv.ofAEval`, starting from the identity `R`-linear equivalence on the
restricted carrier of `M`. The needed compatibility with `X` is definitional.
The local instance `restrictScalarTower` proves compatibility between the
restricted `R`-action and the original polynomial action using
`Polynomial.smul_eq_C_mul` and `mul_smul`.

The underlying functions of `polynomialRoundTrip` are `eₓ.symm` and `eₓ`,
where `eₓ = Module.AEval'.of (xAction R M).hom`.
These formulas are named `polynomialRoundTrip_hom_apply` and
`polynomialRoundTrip_inv_apply`. Its polynomial linearity is exposed concretely
by `polynomialRoundTrip_smul`:

```text
eₓ.symm (p • eₓ(x)) = p • x.
```

The action on the right is the original action on `M`, for every `p : R[X]`.
Thus this comparison recovers the given polynomial action.
`polynomialRoundTripLinear` restricts the same isomorphism to an `R`-linear
equivalence, and `polynomialRoundTripLinear_intertwines` proves that it
intertwines the two `X`-endomorphisms, by polynomial linearity at `X`.

`endomorphismRoundTripLinear R A` identifies the underlying `R`-module of
`F.obj (G.obj A)` with `A.a`. Its functions are `eₐ.symm` and `eₐ`; additivity
and inverse identities are definitional, while scalar compatibility uses
`Module.AEval.C_smul` and linearity of `eₐ`.
`endomorphismRoundTripLinear_intertwines` proves that it carries the recovered
`X`-action to `A.str`, using `Module.AEval'.of_symm_X_smul`.
`endomorphismRoundTrip R A : F.obj (G.obj A) ≅ A` packages the same linear
equivalence with `Endofunctor.Algebra.isoMk` and that compatibility.
The functions of its two directions are recorded by
`endomorphismRoundTrip_hom_apply` and `endomorphismRoundTrip_inv_apply`.

`unitIso R : 𝟭 (ModuleCat R[X]) ≅ F ⋙ G` has components
`(polynomialRoundTrip R M).symm`.
`counitIso R : G ⋙ F ≅ 𝟭 (EndomorphismCat R)` has components
`endomorphismRoundTrip R A`.
Both are constructed with `NatIso.ofComponents`; naturality is extensional
equality of the same underlying functions. The four formulas
`unitIso_hom_app_apply`, `unitIso_inv_app_apply`,
`counitIso_hom_app_apply`, and `counitIso_inv_app_apply` expose their component
functions as the corresponding carrier identifications and their inverses.

`equivalence` uses exactly `F`, `G`, `unitIso`, and `counitIso`.
Its `functor_unitIso_comp` coherence field is proved by extensionality and
definitional equality: the carrier identification and its inverse cancel.
These comparison equalities are intrinsic checks on this construction; this
module introduces no separate statement targets or later localization theorem
family.

## Universes and imported infrastructure

The coefficient ring is in `Type u` and each module carrier is in `Type v`.
The two levels are independently quantified throughout, including
`equivalence.{u, v}` and `fieldEquivalence.{u, v}`.
The object type of each category lies in `Type (max u (v + 1))`, and its
morphism types lie in `Type v`. There is no requirement `u = v` or `u ≤ v`.

The implementation imports the following Mathlib modules, at project pin
`5ed2965256430c3649e86755f9576b54eca72435`.

| Imported module | Used infrastructure |
| --- | --- |
| `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings` | `ModuleCat.restrictScalars`; also the module category, `ModuleCat.of`, `ModuleCat.ofHom`, conversion between linear equivalences and module isomorphisms, and restriction of isomorphisms. |
| `Mathlib.Algebra.Polynomial.Module.AEval` | `Module.AEval'`, `Module.AEval'.of`, `Module.AEval.C_smul`, `Module.AEval'.X_smul_of`, `Module.AEval'.of_symm_X_smul`, `LinearMap.ofAEval`, and `LinearEquiv.ofAEval`. |
| `Mathlib.CategoryTheory.Endofunctor.Algebra` | `Endofunctor.Algebra`, its morphisms and category instance, and `Endofunctor.Algebra.isoMk`; the imported category infrastructure also supplies functors, `NatIso.ofComponents`, and `CategoryTheory.Equivalence`. |

The concrete polynomial action comes from Mathlib's evaluation module, rather
than an assumed categorical equivalence. The module adds no axioms or proof
holes.

## Scope boundary

This construction covers only the equivalence assertion at the start of
example 5. Localization at powers of `X`, its universal property, full
subcategory or adjunction packaging, the lemma and corollary on PDF page 259,
and localization exactness remain successor obligations.
The example's final assertion about localization for modules over a
`k`-algebra `B` also remains a separate obligation: `B` need not be commutative,
and its treatment must retain or explicitly bridge the book's global
nonunital ring and module conventions on printed page 6 / PDF page 12.
The unital commutative-ring generalization here makes no claim to cover that
assertion.
