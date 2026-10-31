# Canonical affine sections comparison over a pushout of base rings

Fix an arbitrary universe `u` and commutative rings
`R S A B : CommRingCat.{u}`. There are specified algebra structures
`R → S`, `R → A`, `R → B`, `A → B`, and `S → B`, with
`IsScalarTower R A B`, `IsScalarTower R S B`, and
`Algebra.IsPushout R S A B`. Thus `B` is the pushout of `S` and `A` over `R`,
with the stated compatible maps. Write

- `f = Spec.map (algebraMap R A) : Spec A → Spec R`;
- `f' = Spec.map (algebraMap S B) : Spec B → Spec S`;
- `g = Spec.map (algebraMap A B) : Spec B → Spec A`;
- `p = Spec.map (algebraMap R S) : Spec S → Spec R`.

The algebra maps in these expressions are bundled with `CommRingCat.ofHom`.
The scalar towers give the commutative square `g ≫ f = f' ≫ p`.
The file constructs ordinary affine sections comparisons for actual module
sheaves `M : (Spec A).Modules`.

`pushoutAffineSectionsPullbackMap R S A B M` is the semilinear map

`Γ_R(f_* M) → Res_R^S Γ_S(f'_* g^* M)`.

Here `Γ_R` and `Γ_S` are Mathlib's `moduleSpecΓFunctor` on the respective spectra,
and the pullback and pushforwards are the actual scheme module functors. The map
first uses `pushforwardΓIso` to identify `Γ_R(f_* M)` with
`Res_R^A Γ_A(M)`. It then applies `Res_R^A` to
`affineSectionsPullbackMap (algebraMap A B) M`, which is induced by the actual
pullback unit `η_M : M → g_*g^*M`. The identity-on-elements
`pushoutRestrictScalarsIso` changes the composite restriction through `A` to
the composite restriction through `S`. Finally the inverse `pushforwardΓIso`
identifies `Res_S^B Γ_B(g^*M)` with `Γ_S(f'_*g^*M)`.
`pushoutAffineSectionsPullbackMap_apply` states that the resulting value on a
global section `m` is exactly `η_M.app ⊤ m`, under these carrier identifications.
This map and its coefficient naturality need only the compatible algebra
square; they do not use the pushout hypothesis.

`pushoutAffineScalarSectionsMap` is the adjunct under Mathlib's
extension/restriction scalar adjunction. Its source and target in `ModuleCat S`
are

`S ⊗_R Γ_R(f_*M) → Γ_S(f'_*g^*M)`.

The Hom-equivalence identity, scalar-unit identity and value on `1 ⊗ m` identify
this specified morphism with the preceding pullback-induced map. Its coefficient
naturality is the commutative square for an arbitrary sheaf morphism `a : M → N`,
using extension of `Γ_R(f_*a)` in the source and `Γ_S(f'_*g^*a)` in the target.
These identities also require no pushout or quasi-coherence assumption.

The factorization `pushoutAffineScalarSectionsMap_eq` identifies the same
canonical adjunct with the composite of four maps:

1. Scalar extension of the `pushforwardΓIso` for `f`;
2. `pushoutScalarTensorIso` on `Γ_A(M)`;
3. Restriction to `S` of `affineScalarSectionsMap (algebraMap A B) M`;
4. The inverse `pushforwardΓIso` for `f'`.

For every `A`-module `V`, `pushoutScalarTensorIso` is an isomorphism
`S ⊗_R Res_R^A V ≅ Res_S^B (B ⊗_A V)` in the actual categorical scalar
extension and restriction conventions. Its forward map sends
`s ⊗ v` to `algebraMap S B s ⊗ v`, and is natural in `V`.
If `M` is quasi-coherent, the affine scalar sections map in the third step is an
isomorphism by `AffineSectionsBaseChange`. Every other factor is an isomorphism.
The instance `isIso_pushoutAffineScalarSectionsMap` therefore proves
invertibility of the specified canonical map, and
`pushoutAffineScalarSectionsIso` packages it as an isomorphism.

The proof of the restriction-square identification composes Mathlib's
`restrictScalarsComp'App` isomorphisms using the two scalar towers. The coefficient
naturality of the semilinear map is obtained by evaluating naturality of `η`
at the top open and at `m`. Scalar adjunction transfers this equality to the
scalar-linear map. The factorization is proved by scalar-extension
extensionality on `1 ⊗ m`, using the tensor cancellation generator formula and
`affineScalarSectionsMap_one_tmul`.

The tensor cancellation mathematics is reused directly from
`Algebra.IsPushout.cancelBaseChange` in pinned Mathlib
`Mathlib/RingTheory/IsTensorProduct.lean`, commit
`5ed2965256430c3649e86755f9576b54eca72435`. The published
`extendScalarsAlgebraIso` changes between the native algebra tensor product and
categorical scalar extension. `pushoutTensorToExtendScalarsEquiv` retains the
`S` action using the scalar tower and the `B`-linearity of this change of
convention. The tensor generator formula follows from Mathlib's cancellation
formula and the identity on pure tensors of the convention change. Its
naturality follows by scalar-extension extensionality on generators. The sheaf
part reuses `TildePullback` and `AffineSectionsBaseChange`, together with the
actual pullback unit and scalar adjunction in pinned Mathlib. These are internal
consequences of the existing constructions; no new external mathematical
assertion is used. The local transparency option supports elaboration through
scheme-module and scalar restriction wrappers.

No flatness, noetherian, reducedness, finiteness or nonzero-ring hypothesis is
assumed. Quasi-coherence is required only for the sheaf section isomorphism.
This file concerns ordinary sections for the specified affine algebra square.
It does not assert higher cohomology base change, a Čech comparison, an
identification with the separately defined derived base-change morphism, or the
relative cube theorem.
