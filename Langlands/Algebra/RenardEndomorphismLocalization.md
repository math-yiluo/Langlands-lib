# Localization of a linear endomorphism at the powers of X (Renard A.III.1, example 5)

Author: Worker 751, who read the original passage and the errata pages cited
below, and implemented the Lean construction and proofs. Worker 709 specified
the task and its scope.

The module `Langlands/Algebra/RenardEndomorphismLocalization.lean` constructs,
for a linear endomorphism `a` of an arbitrary module V, the actual localized pair
`(V_a, ã)` and the canonical map `ι : V → V_a`. It proves that ã is invertible,
that ι intertwines a with ã, gives formulas on fractions, and proves the
universal property of the pair. Every declaration below lives in the namespace
`Langlands.Renard.EndomorphismLocalization`.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, Appendix A.III.1, example 5 ("Localisé d'un espace
vectoriel relativement à un endomorphisme"), printed page 252 / PDF page 258.
Registered source `renard-2026-representations-groupes-reductifs-padiques`,
file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`
(checked). Printed page = PDF page minus 6.

Other passages used:

- The right universal problem, printed pages 251–252 / PDF pages 257–258.
- Example 4 (localization of a module), printed page 252 / PDF page 258. The
  source gets example 5 from it through the k[X]-module equivalence.
- The lemma after example 5, printed page 253 / PDF page 259. It is used only
  to justify the inverse-shift reading of fractions: its part (ii) describes the
  localized space as `⋃ₙ (ã')⁻ⁿ(L')`. The lemma itself is not formalized here.
- The module convention, PDF page 12: `M(A)` denotes unital modules.

From the supplementary errata `renard-2010-corrections-complements` (SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`), PDF
pages 17–19 were read. They contain no entry for this example. This was a
limited check, not an exhaustive reading of the errata.

The source statement says the following. Let k be a field and L a k-vector
space with `a ∈ End_k(L)`. Then there is a pair `(L_a, ã)` with ã invertible,
and a morphism `ι : (L, a) → (L_a, ã)`, such that for every morphism
`f : (L, a) → (M, b)` with b invertible there is a unique morphism
`f̃ : (L_a, ã) → (M, b)` with `f = f̃ ∘ ι`. Here a morphism of pairs is a
linear map that intertwines the two endomorphisms.

## Source-to-Lean dictionary

| Source | Lean |
| --- | --- |
| k, L, a | `R` (a field in `FieldStatement`), `V`, `a : Module.End R V` |
| k[X]-module of (L, a) | `EvalModule a` = `Module.AEval' a` |
| `{X^k}_{k ∈ ℕ}` | `powersX R` = `Submonoid.powers (X : R[X])` |
| `L_a` | `Localized a` |
| ã | `localizedEnd a`; as an automorphism, `localizedEquiv a` |
| ã⁻¹ | `localizedInv a` |
| ι | `iota a` |
| (M, b), with b invertible | `W`, `b : Module.End R W` with `hb : IsUnit b` |
| f | `f : V →ₗ[R] W` with `hf : ∀ v, f (a v) = b (f v)` |
| f̃ | `factor a b hb f hf` |

The source gives no separate proof for example 5; it obtains the pair from
example 4 through the equivalence of categories. The Lean proofs below follow that route on actual
objects, with the published module-localization interface.

## Hypotheses, universes and the extension to rings

All general declarations assume exactly a commutative unital ring
`R : Type u` with `[CommRing R]`, a module `V : Type v` with
`[AddCommGroup V] [Module R V]`, and an endomorphism `a : Module.End R V`.
Where a target is used, it is `W : Type w` with `[AddCommGroup W] [Module R W]`
and `b : Module.End R W`. The universes u, v and w are independent. The
predicate `HasUniversalProperty` also takes a carrier `L : Type x` in a fourth
independent universe.

The constructed carrier `Localized a` lives in `Type (max u v)`, the universe
of Mathlib's `LocalizedModule`. No `Small` instance or universe shrinking is
used. There are no hypotheses of finite dimension, finite generation,
noetherianity, nontriviality of R or V, nonzero a, or injectivity of a; in
particular a may be zero or nilpotent.

Working over a commutative ring instead of a field is an implementation
extension; the source only treats fields. The exact field case is the checked
specialization `FieldStatement` below.

## The actual models

- `EvalModule a : Type v` is an abbreviation for Mathlib's
  `Module.AEval' a`. This is the R[X]-module with the additive group of V in
  which X acts as a. Elements enter through the R-linear equivalence
  `Module.AEval'.of a : V ≃ₗ[R] Module.AEval' a`. Mathlib's
  `Module.AEval'.X_smul_of` gives `X • of a v = of a (a v)`.
- `powersX R : Submonoid R[X]` is an abbreviation for
  `Submonoid.powers X`.
- `Localized a : Type (max u v)` is an abbreviation for
  `LocalizedModule (powersX R) (EvalModule a)`, Mathlib's actual localized
  module. No new quotient and no `IsLocalizedModule` certificate replaces it.
  Its additive group is Mathlib's. Its R-module structure is found by instance
  search: it is Mathlib's Ore-localization instance
  `OreLocalization.instModuleOfIsScalarTower` (in
  `Mathlib/RingTheory/OreLocalization/Ring.lean`), applied to the scalar tower
  R → R[X] → `EvalModule a`. `smul_eq_C_smul a r z` proves
  `r • z = (C r : R[X]) • z`. So the R-action is the restriction of the
  R[X]-action along the constant polynomials.
- `toPolynomialObj_eq A` proves, by `rfl`, that for every object
  `A : Langlands.Algebra.PolynomialEndomorphism.EndomorphismCat.{u, v} R` the
  published object map gives
  `toPolynomialObj R A = ModuleCat.of R[X] (EvalModule (endomorphism R A))`.
  So the evaluation module used here is the carrier of the published
  polynomial-module equivalence (`equivalence`, and `fieldEquivalence` for
  fields). That equivalence is not rebuilt; this unit works directly with its
  object-level module.

## Canonical map

`iota a : V →ₗ[R] Localized a` is the composite of
`(Module.AEval'.of a).toLinearMap` with
`(LocalizedModule.mkLinearMap (powersX R) (EvalModule a)).restrictScalars R`.
`iota_def` records this formula. `iota_apply a v` states
`iota a v = LocalizedModule.mk (Module.AEval'.of a v) 1`, which is the
fraction `v / 1`.

## The invertible endomorphism ã

- `localizedEnd a : Module.End R (Localized a)` is multiplication by X: the
  R[X]-linear scalar endomorphism
  `algebraMap R[X] (Module.End R[X] (Localized a)) X`, restricted to R.
  `localizedEnd_apply` states `localizedEnd a z = (X : R[X]) • z`.
- `localizedInv a` is Mathlib's division by X, namely
  `LocalizedModule.divBy ⟨X, Submonoid.mem_powers X⟩` restricted to R
  (`localizedInv_apply`).
- `localizedEnd_localizedInv a z` and `localizedInv_localizedEnd a z` are the
  two inverse identities `ã (ã⁻¹ z) = z` and `ã⁻¹ (ã z) = z`. They apply the
  published `Langlands.Renard.ModuleLocalization.scalar_divBy` and
  `divBy_scalar` to the denominator X. `localizedEnd_mul_localizedInv` and
  `localizedInv_mul_localizedEnd` state the same identities as products in
  `Module.End R (Localized a)`.
- `localizedEquiv a : Localized a ≃ₗ[R] Localized a` is the R-linear
  automorphism `LinearEquiv.ofLinearMap` built from these two maps.
  `localizedEquiv_apply` and `localizedEquiv_symm_apply` say its forward map
  is `localizedEnd a` and its inverse is `localizedInv a`.
- `isUnit_localizedEnd a : IsUnit (localizedEnd a)` gives the unit with
  inverse `localizedInv a`. Invertibility is proved from the localization; it
  is not a hypothesis.
- `iota_intertwines a v : iota a (a v) = localizedEnd a (iota a v)` is the
  canonical intertwining identity `ι (a v) = ã (ι v)`. The proof rewrites with
  `LocalizedModule.smul'_mk` and `Module.AEval'.X_smul_of`.
- `localizedEnd_pow_apply a n z : (localizedEnd a ^ n) z = (X ^ n : R[X]) • z`,
  by induction on n.

## Fractions

Notation: `frac a v n : Localized a` is the fraction written `v / Xⁿ`.
By definition it is the actual `LocalizedModule` class

```lean
LocalizedModule.mk (Module.AEval'.of a v) (Submonoid.pow X n)
```

where `Submonoid.pow X n : Submonoid.powers X` is the element `X ^ n`. The
numerator is the image of v in the evaluation module. The laws are:

- `frac_zero a v : frac a v 0 = iota a v`.
- `localizedEnd_frac a v n : localizedEnd a (frac a v n) = frac a (a v) n`
  (X action: `ã (v / Xⁿ) = a v / Xⁿ`).
- `localizedInv_frac a v n : localizedInv a (frac a v n) = frac a v (n + 1)`
  (inverse action: `ã⁻¹ (v / Xⁿ) = v / Xⁿ⁺¹`). It is proved from the
  published `ModuleLocalization.divBy_mk`.
- `localizedEnd_frac_succ a v n : localizedEnd a (frac a v (n + 1)) = frac a v n`.
- `frac_eq_localizedInv_pow a v n : frac a v n = (localizedInv a ^ n) (iota a v)`,
  the inverse-shift identity `v / Xⁿ = ã⁻ⁿ (ι v)`. It matches the source's
  inverse-shift description on PDF page 259.
- `localizedEnd_pow_frac a v n : (localizedEnd a ^ n) (frac a v n) = iota a v`,
  proved with `LocalizedModule.mk_cancel`.
- `frac_add a v w n` and `frac_smul a r v n`: the fraction is additive and
  R-linear in its numerator for a fixed denominator.
- `frac_surjective a z : ∃ (v : V) (n : ℕ), frac a v n = z`. Every element of
  `Localized a` is a fraction with denominator a power of X. With
  `frac_eq_localizedInv_pow`, this gives every element in the form
  `ã⁻ⁿ (ι v)`. No separate set-union declaration is stated.
- `frac_eq_frac_iff a v w m n`:
  `frac a v m = frac a w n ↔ ∃ k : ℕ, (a ^ (k + n)) v = (a ^ (k + m)) w`.
  This is Mathlib's relation `LocalizedModule.mk_eq`, translated through
  `Module.AEval'.X_pow_smul_of` and the injectivity of `Module.AEval'.of a`.

## The universal property

For `L : Type x` with `[AddCommGroup L] [Module R L]`, an endomorphism
`a : Module.End R V`, `aL : Module.End R L` and `ι : V →ₗ[R] L`,
`HasUniversalProperty a aL ι : Prop` is

```lean
∀ (W : Type w) [AddCommGroup W] [Module R W] (b : Module.End R W), IsUnit b →
  ∀ f : V →ₗ[R] W, (∀ v, f (a v) = b (f v)) →
    ∃! g : L →ₗ[R] W, (∀ z, g (aL z) = b (g z)) ∧ g.comp ι = f
```

Its universe parameters are in the order u, v, x, w (ring, source, carrier,
target). Following the source, it assumes only that b is invertible, through
`IsUnit b` in `Module.End R W`. It assumes nothing about f beyond linearity and
the intertwining equation. The unique g must intertwine `aL` with b and satisfy
`g ∘ ι = f`. The predicate does not itself require `aL` to be invertible or ι
to intertwine; those are separate conjuncts of `FieldStatement`.

The construction of the factorization:

- `evalModule_isSLocal b hb : ModuleLocalization.IsSLocal (powersX R) (EvalModule b)`
  for `hb : IsUnit b`. After `ModuleLocalization.isSLocal_iff_bijective`, the
  action of `X ^ n` on `EvalModule b` equals `of b ∘ bⁿ ∘ (of b)⁻¹`, by
  `Module.AEval'.X_pow_smul_of`. This map is bijective because `b ^ n` is a
  unit (`IsUnit.pow` and `Module.End.isUnit_iff`).
- `polyMap a b f hf : EvalModule a →ₗ[R[X]] EvalModule b` is
  `LinearMap.ofAEval a ((Module.AEval'.of b).toLinearMap.comp f) _`. Its
  compatibility condition comes from hf and `Module.AEval'.X_smul_of`.
  `polyMap_of` states `polyMap a b f hf (of a v) = of b (f v)`.
- `factor a b hb f hf : Localized a →ₗ[R] W` is
  `(Module.AEval'.of b).symm.toLinearMap.comp ((ModuleLocalization.factor (powersX R) (evalModule_isSLocal b hb) (polyMap a b f hf)).restrictScalars R)`
  (`factor_apply`). That is, it is the published localized-module lift
  `ModuleLocalization.factor` of `polyMap`, read back in W.
- `factor_intertwines`: `factor (localizedEnd a z) = b (factor z)`. This holds
  because the lift is R[X]-linear (`map_smul` for X) and by
  `Module.AEval'.of_symm_X_smul`.
- `factor_comp_iota`: `(factor a b hb f hf).comp (iota a) = f`, by the published
  `ModuleLocalization.factor_comp` and `polyMap_of`.
- `factor_frac a b hb f hf v n`:

  ```lean
  factor a b hb f hf (frac a v n) =
    ((hb.unit⁻¹ ^ n : (Module.End R W)ˣ) : Module.End R W) (f v)
  ```

  This is the representative formula `f̃ (v / Xⁿ) = b⁻ⁿ (f v)`. Here `b⁻¹` is
  the inverse of b in the unit group of `Module.End R W`. It is an
  endomorphism of W, not a scalar of R.
- `pow_apply_frac a b g hg v n`: any R-linear `g : Localized a →ₗ[R] W` with
  `hg : ∀ z, g (localizedEnd a z) = b (g z)` satisfies
  `(b ^ n) (g (frac a v n)) = g (iota a v)`. The proof shows
  `g ∘ ãⁿ = bⁿ ∘ g` by induction and applies `localizedEnd_pow_frac`.
- `eq_of_intertwines a b hb g g' hg hg' h`: assume `hb : Function.Injective b`,
  that g and g' both intertwine `localizedEnd a` with b, and
  `h : g.comp (iota a) = g'.comp (iota a)`. Then `g = g'`. The proof writes
  each element as `frac a v n` (`frac_surjective`), applies
  `pow_apply_frac` and cancels the injective map `b ^ n`.
- `factor_unique a b hb f hf g hg hgf`: every intertwining g with
  `g.comp (iota a) = f` equals `factor a b hb f hf`. It applies
  `eq_of_intertwines`, with b injective by `Module.End.isUnit_iff`.
- `hasUniversalProperty a` proves
  `HasUniversalProperty.{u, v, max u v, w} a (localizedEnd a) (iota a)` for every
  independent target universe w. The witness is `factor`, with
  `factor_intertwines`, `factor_comp_iota` and `factor_unique`.

## Field specialization

`FieldStatement.{u, v, w} : Prop` is

```lean
∀ (k : Type u) [Field k] (V : Type v) [AddCommGroup V] [Module k V]
    (a : Module.End k V),
  IsUnit (localizedEnd a) ∧ (∀ v, iota a (a v) = localizedEnd a (iota a v)) ∧
    HasUniversalProperty.{u, v, max u v, w} a (localizedEnd a) (iota a)
```

Here the general declarations are instantiated at the commutative ring
underlying the field k. The theorem `fieldStatement : FieldStatement.{u, v, w}`
proves it from `isUnit_localizedEnd`, `iota_intertwines` and
`hasUniversalProperty`. This is the source's example 5, with V of arbitrary
dimension and the target W in an independent universe. Lean inspection reports
that `FieldStatement` and `HasUniversalProperty` return `Prop`. `fieldStatement`
depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Reuse

Published Library declarations reused by name:
`Langlands.Renard.ModuleLocalization.{IsSLocal, isSLocal_iff_bijective, factor, factor_comp, divBy_scalar, scalar_divBy, divBy_mk}`
(Worker 618, Renard example 4) and
`Langlands.Algebra.PolynomialEndomorphism.{EndomorphismCat, endomorphism, toPolynomialObj}`.
Mathlib (pinned commit `5ed2965256430c3649e86755f9576b54eca72435`) supplies
`Module.AEval'` and its lemmas `of`, `X_smul_of`, `X_pow_smul_of` and
`of_symm_X_smul`, and `LinearMap.ofAEval`, from
`Mathlib/Algebra/Polynomial/Module/AEval.lean`. It supplies `LocalizedModule`,
`mk`, `mkLinearMap`, `divBy`, `mk_eq`, `smul'_mk`, `mk_cancel` and
`induction_on` from `Mathlib/Algebra/Module/LocalizedModule/Basic.lean`, and
`Module.End.isUnit_iff`. No axioms are added.

## Scope

This unit does not formalize:

- the category of pairs, the full subcategory of pairs with invertible
  endomorphism, or an adjunction or universal-arrow packaging;
- the extension in the example's last sentence to a k-algebra B and
  endomorphisms of B-modules (possibly noncommutative or nonunital); it is not
  inferred from this unital polynomial-module model;
- the lemma and corollary on PDF page 259 (injectivity of ι for injective a,
  the kernel union `K = ⋃ ker aⁿ`, the quotient `L / K` and its comparison);
- exactness of localization;
- the finite-localization proposition of Appendix C.II (printed page 279 / PDF
  page 285).

These remain parent obligations.
