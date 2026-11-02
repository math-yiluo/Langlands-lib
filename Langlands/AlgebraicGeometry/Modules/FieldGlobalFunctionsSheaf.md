# The canonical arbitrary-base global-functions sheaf comparison

For an arbitrary field `k : Type u`, a proper morphism `f : X → Spec k`,
and an actual Cartesian square

```text
Y --g--> X
|        |
p        f
|        |
v        v
T --t--> Spec k,
```

`FieldGlobalFunctions.directImageSheafIso` constructs the isomorphism of
actual structure modules on the arbitrary scheme `T`

```text
t^*(Gamma(X, O_X))^~  ≅  p_* O_Y.
```

Here `sections f` is the actual module of global functions with scalar
action through the structure morphism. No identification of global functions
with `k` is assumed. There are no additional hypotheses on `T`, and the
statement retains the universe parameter `u`. In particular `T` may be
nonreduced or non-quasi-compact. The source is the scheme-module pullback
of the associated module on `Spec k`; the target is the actual scheme-module
pushforward of the structure module of `Y`.

The forward map is specified, rather than chosen merely from an existence
assertion. For any commuting square over an arbitrary commutative ring `R`,
`directImageGlobalSectionsMap` is the actual pullback of functions, transported
through pushforward composition and the equality of the two structure maps.
Its value on `x` is `g.appTop x`. The composite of the associated-sheaf and
scheme pullback adjunctions then defines `directImageSheafMap`.
`directImageSheafIso_hom` identifies the isomorphism's forward map with
this canonical morphism.

The proof of invertibility uses the following local comparisons.

1. For an affine open immersion `j : Spec S → T` and a ring map `φ : R → S`
   with `j ≫ t = Spec.map φ`, actual global sections after pushforward along
   `j` agree with restriction of scalars along `φ`. Uniqueness of left
   adjoints gives `tildeRestrictionIso`, identifying restriction of
   `t^*(M^~)` with the associated module of scalar extension of `M`.
2. `tildeRestriction_homEquiv` identifies the scalar-extension adjunct of a
   restricted morphism with its original global-sections adjunct followed
   by actual restriction. `tildeRestriction_one_tmul` computes this identity
   on `1 tensor x`; the coherence maps on global sections are identity maps.
3. `affineChartSectionsIso` identifies the actual global sections on
   `Spec Gamma(T,U)` after chart restriction with sections on `U`, including
   the `Gamma(T,U)` scalar action. Its naturality holds for every morphism
   of structure modules. It uses the actual restriction maps and the
   scalar-action lemmas from `AffineVanishing.QuasicoherentCech`.
4. Applied to `directImageSheafMap`, these comparisons show that
   `directImageAffineModuleMap` sends `1 tensor x` to the restriction of
   `g.appTop x` to `p^-1 U`. The canonical affine base-change isomorphism
   `directImageAffineSectionsIso` has exactly the same value, by
   `baseChangeIso_hom_one_tmul`, the actual inverse-open `topIso`, and the
   formula for pullback along a composite. The scalar-extension universal
   property therefore identifies the two module maps.
5. The affine section map is an isomorphism. Cancel the associated-sheaf
   adjunction unit and the affine-chart comparison, both isomorphisms, to
   obtain invertibility of the canonical sheaf map on sections of `U`.
   This argument uses only sections on each affine open; it does not infer
   an entire affine sheaf morphism is invertible from its top sections.
6. Apply `TopCat.Sheaf.isIso_iff_isIso_basis` to the basis of all affine
   opens of `T`, and reflect isomorphisms through the forgetful functor to
   additive presheaves. This proves `isIso_directImageSheafMap` globally
   and constructs `directImageSheafIso`.

This is an internal consequence of the canonical module base-change result
in `FieldGlobalFunctions`, its actual affine-open version in
`FieldGlobalFunctionsDirectImage`, and the generator formula in
`FieldGlobalFunctionsAlgebra`, together with Mathlib's module adjunctions,
uniqueness of left adjoints, and the affine-basis sheaf criterion. The
construction of `affineChartSectionsIso` generalizes the private
`affineChartSectionsEquiv` used in the published
`FiniteFlatPushforwardGenericBasisProof`; it exposes the actual forward
map and its naturality for use here. No new literature translation or
representability assumption enters this derivation.

The small corollary `directImageFreeIso` chooses a basis of the finite
`k`-module `sections f`, indexed by
`ULift (Fin (Module.finrank k (sections f)))`. The basis representation,
`tildeFinsupp`, and the actual `freePullbackIso` identify the source of
`directImageSheafIso` with the finite free structure module on that index
type over `T`. Composing gives a global finite free trivialization of the
actual direct image. The basis choice is not asserted to be canonical.
`directImageSectionBasis` then applies the published `globalSectionBasis`
construction to give a basis of `directImageSections p V` over `Gamma(T,V)`
for every open `V`, without an affine-open or quasi-compactness hypothesis.
The index type has cardinality `dim_k Gamma(X,O_X)`. This includes rank zero;
no nonemptiness assumption on `X` or `T` is used.

This result is a direct-image comparison prerequisite for the proper-field
Picard argument. It does not assert Picard algebraicity, identify Picard
sheafification topologies, construct a representing scheme, or prove
`FieldPicardSheafRepresentabilityStatement`.
