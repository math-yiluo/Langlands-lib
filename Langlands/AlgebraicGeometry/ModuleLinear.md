# Scalars on morphisms of scheme modules

For any `AlgebraicGeometry.Scheme.{u}` S, this module constructs scalar multiplication on the morphisms of Mathlib's actual category `S.Modules`. The scalars are global regular functions, `Γ(S, ⊤)`. No affineness, quasicoherence, finiteness, smoothness, or local-freeness hypothesis is used.

`Langlands.Scheme.Modules.restrictScalar U` is the ring homomorphism restricting a global regular function to an open U. For an O_S-linear sheaf morphism f : M → N, `scalarHom r f` has the following map on U-sections:

```
(scalarHom r f).app U x = restrictScalar U r • f.app U x.
```

Each component is O_S(U)-linear because O_S(U) is commutative. Naturality is proved using naturality of f, semilinearity of the restriction maps of N, and functoriality of restriction of regular functions (`restrictScalar_map`). Thus this is a morphism of the existing module sheaves. Their objects and sheaf conditions are inherited from Mathlib.

`globalHomSMul` and `globalHomModule` provide the resulting scalar action and module structure on M → N. `global_smul_app` states the section formula for the inferred action. All module axioms are proved by extensionality on opens and sections. `globalSectionsLinear` proves that composition is bilinear, again on sections; the proof for postcomposition uses the O_S(U)-linearity of the second morphism. This supplies `CategoryTheory.Linear Γ(S, ⊤) S.Modules`.

For any commutative ring R and an actual ring homomorphism a : R → Γ(S, ⊤), `linearOfGlobalScalars a` restricts these scalars and constructs `Linear R S.Modules`. `endAlgebra a M` uses this structure and Mathlib's endomorphism-algebra construction to give `Algebra R (CategoryTheory.End M)`. Its multiplication convention is f * g = g ≫ f, so f acts after g. `endAlgebra_map_app` proves that its scalar algebra map sends r to multiplication on sections by the restriction of a(r).

`scalarsFromBase p`, for p : S → Spec R with `R : CommRingCat.{u}`, constructs the global ring homomorphism by composing Mathlib's inverse `Scheme.ΓSpecIso R` with `p.appTop`. `linearOverBase p` therefore makes the actual category of module sheaves on S linear over R. If R has a Q-algebra structure, `rationalLinearOverBase p` composes with Q → R and makes that category Q-linear. In particular, this applies to schemes over the spectrum of a universe-compatible copy of Q. The supplied structure morphism and scalar ring homomorphisms are actual maps, not assumed module or endomorphism actions.

The provenance is a derived algebraic construction from the pinned Mathlib modules `AlgebraicGeometry.Modules.Sheaf`, `Algebra.Category.ModuleCat.Presheaf`, `AlgebraicGeometry.Scheme`, and `CategoryTheory.Linear.Basic`. The construction uses their existing local section modules, restriction maps, categorical Hom and End, `Module.compHom`, and `CategoryTheory.Linear` endomorphism-algebra instance. The new scalar maps and all compatibility laws are implemented above; no external geometric theorem is asserted or used.

This is a prerequisite for extending a future Lie-module endomorphism action to rational endomorphisms. It constructs neither the Lie module nor its differential, and does not yet extend an action or an additive functor across rationalization.
