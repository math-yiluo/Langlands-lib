# Pullback of local module morphisms

For arbitrary schemes X, Y in universe `u`, a scheme morphism f : X → Y,
module sheaves M, N on Y, and an open U of Y, this module constructs

```
localHomPullback f U : LocalHom M N U → LocalHom (f*M) (f*N) (f ⁻¹ᵁ U).
```

Here `f*` denotes Mathlib's actual `AlgebraicGeometry.Scheme.Modules.pullback f`,
and `LocalHom` is the local module-sheaf morphism type from
[ModuleDual](ModuleDual.md). All declarations are in `Langlands.Scheme.Modules`.
No finiteness, flatness or quasicoherence assumption is made.

## Construction

`restrictPullbackNatIso f U` is the natural isomorphism

```
pullback f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι ≅
  restrictFunctor U.ι ⋙ pullback (f ∣_ U).
```

It first identifies restriction with pullback along the open immersion, uses
`pullbackComp`, transports along the equality
`morphismRestrict_ι f U`, reverses the second pullback composition comparison,
and finally reverses the restriction-to-pullback comparison on Y. These are
Mathlib's existing canonical comparisons. The construction is the natural-functor
version of the pointwise `Langlands.AlgebraicGeometry.Picard.restrictPullbackIso`
from the published Library; it uses no line-bundle hypothesis or Picard structure.

For h : `LocalHom M N U`, `internalHomSectionsEquiv M N U` gives an actual
morphism between the restricted module sheaves on the open subscheme U.
`localHomPullback` applies `pullback (f ∣_ U)` to that morphism and conjugates
by `restrictPullbackNatIso f U`. It then applies the inverse of
`internalHomSectionsEquiv` on X. The proved equation
`internalHomSectionsEquiv_localHomPullback` states this precise formula.

`localHomPullback_zero` and `localHomPullback_add` prove preservation of zero
and addition. They apply injectivity of the section equivalence, its existing
zero and addition laws, additivity of scheme-module pullback, and bilinearity
of composition.

`localHomPullback_naturality` proves compatibility with precomposition and
postcomposition by arbitrary global module-sheaf maps a : M′ → M and b : N → N′:

```
localHomPullback f U (a.over U ≫ h ≫ b.over U) =
  ((pullback f).map a).over (f ⁻¹ᵁ U) ≫
    localHomPullback f U h ≫ ((pullback f).map b).over (f ⁻¹ᵁ U).
```

Its proof uses the naturality of `internalHomSectionsEquiv`, functoriality of
the restricted pullback, and naturality of the hom and inverse of
`restrictPullbackNatIso`.

`localDualPullback f M U` specializes N to the actual structure module on Y,
then postcomposes with the restriction of `(pullbackUnitIso f).hom`. It maps a
section of `dual M` on U to a section of `dual (f*M)` on `f ⁻¹ᵁ U`.
The unit isomorphism is the published canonical structure-module comparison,
not additional data supplied to this construction.

## Source and scope

The original source is the registered `stacks-relative-differentials-internal-hom-2026-10-21`,
*Stacks Project - Relative differentials and internal Hom (HTML snapshot 2026-10-21)*,
folder SHA256 `9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`.
The file `01CM.html`, opening of Section 17.22
([tag 01CM](https://stacks.math.columbia.edu/tag/01CM)), defines internal-Hom
sections as morphisms of restricted module sheaves. Lemma 17.22.5
([tag 0C6I](https://stacks.math.columbia.edu/tag/0C6I)) displays the canonical
pullback comparison. The construction here is the local-map part of that
comparison, derived by applying pullback to the restricted morphism. The
structure-module specialization and the naturality packaging are derived
categorical constructions. The lemma's isomorphism conclusion requires finite
presentation and flatness; it is not asserted or used here.

This is a prerequisite of the global dual comparison. Compatibility with
restriction in U and with scalar multiplication, assembly into a morphism
`f*(dual M) → dual(f*M)`, and its identity and composition laws remain separate
obligations of the host task. The present file does not assume or assert those
remaining laws and does not assert that the dual pullback comparison is an
isomorphism.
