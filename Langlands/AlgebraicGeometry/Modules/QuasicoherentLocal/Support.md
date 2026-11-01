# Vanishing of a module on an open subset

Author: Worker 921.

This helper module is part of the proof of
`Langlands.AlgebraicGeometry.Modules.NoetherianSeparatedQuasicoherentVanishingStatement`. It
records where an `𝒪_X`-module vanishes, which the vanishing induction uses as its notion of
support.

## The property

```lean
def VanishesOn (M : X.Modules) (O : X.Opens) : Prop :=
  ∀ W ≤ O, ∀ s : Γ(M, W), s = 0
```

Every section of `M` over an open contained in `O` is zero. Equivalently, `M|_O` is zero (see
`isZero_restrict` and `of_isZero_restrict`). In the induction, "`M` vanishes off a closed set
`Z`" is `VanishesOn M Z.compl`.

## Declarations

Namespace `Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal`, sub-namespace
`VanishesOn` for the first group.

- `mono`: vanishing on `O` gives vanishing on any `O' ≤ O`.
- `sup`: vanishing on `O` and on `O'` gives vanishing on `O ⊔ O'`. A section over
  `W ≤ O ⊔ O'` restricts to zero on `W ⊓ O` and on `W ⊓ O'`, which cover `W`. So it is zero
  by the sheaf property (Mathlib's `TopCat.Sheaf.eq_of_locally_eq₂`).
- `of_iso`: vanishing passes along an isomorphism of modules.
- `kernel`: if `M` vanishes on `O`, so does `kernel φ` for `φ : M ⟶ N`, because the kernel
  inclusion is injective on sections.
- `isZero_restrict`, `of_isZero_restrict`: `VanishesOn M O` holds if and only if
  `IsZero (M.restrict O.ι)`. The sections of `M.restrict O.ι` over `W` are the sections of
  `M` over `O.ι ''ᵁ W ≤ O`. Conversely, `W ≤ O` equals `O.ι ''ᵁ (O.ι ⁻¹ᵁ W)` (Mathlib's
  `Scheme.Hom.image_preimage_eq_opensRange_inf` and `Scheme.Opens.opensRange_ι`).
- `cokernel_of_right`: if `N` vanishes on `O`, so does `cokernel φ` for `φ : M ⟶ N`.
  Restriction to `O` preserves cokernels, being a left adjoint. A morphism into the zero
  module `N|_O` is an epimorphism, so its cokernel is zero.
- `cokernel_of_isIso`: if `φ|_O` is an isomorphism, `cokernel φ` vanishes on `O`.

For an open immersion `j : Y ⟶ X`:

- `unitMap j M : M ⟶ j_* (M.restrict j)` is the unit of Mathlib's
  `Scheme.Modules.restrictAdjunction j`. Over an open `W` it is the restriction
  `M(W) ⟶ M(j ''ᵁ j ⁻¹ᵁ W)`.
- `isIso_unitMap_app`: for `W ≤ j.opensRange` this restriction is along an equality of opens,
  hence an isomorphism.
- `isIso_restrict_unitMap`: for `O ≤ j.opensRange`, the restriction of `unitMap j M` to `O`
  is an isomorphism (componentwise, by `Scheme.Modules.Hom.isIso_iff_isIso_app`).
- `vanishesOn_kernel_unitMap`, `vanishesOn_cokernel_unitMap`: the kernel and the cokernel of
  `unitMap j M` vanish on `j.opensRange`.
- `vanishesOn_pushforward_restrict`: the sections of `j_* (M.restrict j)` over `W` are the
  sections of `M` over `j ''ᵁ j ⁻¹ᵁ W`. So if `M` vanishes on `O'` and
  `j ''ᵁ j ⁻¹ᵁ W ≤ O'` for all `W ≤ O`, then `j_* (M.restrict j)` vanishes on `O`.

## Provenance

Internal infrastructure with no separate literature source: elementary support bookkeeping for
sheaves of modules.
