# Kernels, cokernels and pushforwards of modules that are quasi-coherent on affine opens

Author: Worker 921.

This helper module is part of the proof of
`Langlands.AlgebraicGeometry.Modules.NoetherianSeparatedQuasicoherentVanishingStatement`. It
introduces the property of an `𝒪_X`-module used in the vanishing induction and shows that the
property is preserved by kernels, cokernels, isomorphisms and affine pushforwards.

## The property

```lean
def IsAffineLocallyQuasicoherent (M : X.Modules) : Prop :=
  ∀ (V : X.Opens) (hV : IsAffineOpen V), (M.restrict hV.fromSpec).IsQuasicoherent
```

For every affine open `V`, the restriction of `M` along Mathlib's open immersion
`hV.fromSpec : Spec Γ(X, V) ⟶ X` is quasi-coherent (Mathlib's
`SheafOfModules.IsQuasicoherent`). Every quasi-coherent module has this property. The
induction works with it so that it never has to glue quasi-coherence of kernels and
cokernels from local data.

## Declarations

Namespace `Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal`.

Sections of kernels, for `φ : M ⟶ N` in `X.Modules`:

- `res_app`: `φ.app` commutes with restriction of sections.
- `app_kernel_ι_app`: `φ.app W ((kernel.ι φ).app W k) = 0`.
- `injective_app_of_mono`: a monomorphism of sheaves of abelian groups is
  injective on sections.
- `kernel_ι_app_injective`: `(kernel.ι φ).app W` is injective.
- `exists_kernel_ι_app_eq`: a section `m` of `M` over `W` with `φ.app W m = 0` comes from a
  section of `kernel φ`.

The last two apply Mathlib's `TopCat.Sheaf.sections_exact_of_left_exact` and mono
preservation to the image of `kernel φ ⟶ M ⟶ N` under the Library's exact forgetful functor
`PushforwardInjectiveAcyclic.toAbSheaf X`.

Localization property (`IsLocalizingAt` from `QuasicoherentLocal.Basic`):

- `isLocalizingAt_kernel`: if `M` and `N` have the property over `V`, so does `kernel φ`. To
  extend a section `s` of the kernel over `D(h)`, extend it in `M` to `t` with
  `res t = h^n • s`. Then `φ t` vanishes on `D(h)`, so `h^m • φ t = 0`. Hence `h^m • t` lies
  in the kernel, and it restricts to `h^(m+n) • s`, by injectivity of the kernel inclusion.
  The torsion statement follows from that of `M` and injectivity.
- `pushforward_smul`: for `j : Y ⟶ X`, `r : Γ(X, W)` acts on
  `Γ(j_* G, W) = Γ(G, j ⁻¹ᵁ W)` through `j.app W r` (definitional).
- `app_rres`: `j.app` commutes with restriction of functions (naturality of `j.app`).
- `isLocalizingAt_pushforward`: if `G` has the property over `j ⁻¹ᵁ U`, then `j_* G` has it
  over `U`. The proof uses `j ⁻¹ᵁ X.basicOpen h = Y.basicOpen (j.app U h)` (Mathlib's
  `Scheme.preimage_basicOpen`).

Cokernels on `Spec R`:

- `isQuasicoherent_cokernel_spec`: on `Spec R`, the cokernel of a morphism `φ` of
  quasi-coherent modules is quasi-coherent. By Mathlib, the counit
  `Scheme.Modules.fromTildeΓNatTrans` is an isomorphism on quasi-coherent modules. So `φ` is
  isomorphic, as an arrow, to `tilde` of the map on global sections, and
  `cokernel φ ≅ tilde (cokernel (Γ φ))` since `tilde.functor R` is a left adjoint and
  preserves cokernels. Tilde modules are quasi-coherent (Mathlib instance).

The property:

- `IsAffineLocallyQuasicoherent.of_isQuasicoherent`: from Mathlib's instance
  `Scheme.Modules.isQuasicoherent_restrictFunctor`.
- `.of_iso`: restriction preserves isomorphisms and quasi-coherence is isomorphism-closed.
- `.kernel`: by `isLocalizingAt_of_isQuasicoherent`, then `isLocalizingAt_kernel`, then
  `isQuasicoherent_of_isLocalizingAt`.
- `.cokernel`: restriction along an open immersion is a left adjoint
  (`Scheme.Modules.restrictAdjunction`), so it preserves cokernels. Then apply
  `isQuasicoherent_cokernel_spec` on `Spec Γ(X, V)`.
- `.pushforward (j : Y ⟶ X) [IsAffineHom j]`: for an affine open `U`, `j ⁻¹ᵁ U` is affine
  (`IsAffineOpen.preimage`). Then combine `isLocalizingAt_of_isQuasicoherent` for `G`,
  `isLocalizingAt_pushforward` and `isQuasicoherent_of_isLocalizingAt`.

## Provenance

Internal infrastructure with no separate literature source. These are the standard facts that
quasi-coherent modules are closed under kernels and cokernels and under pushforward along
affine morphisms. Here they are stated for the weaker property `IsAffineLocallyQuasicoherent`,
which is all the vanishing induction needs.
