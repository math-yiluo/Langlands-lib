/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Single
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-! # Shifted Koszul complexes and their augmentations

Source: Stacks Project, Tag 08CX, Section 36.9
(blueprint: def-pc-shifted-koszul-augmentation).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

/-- Square zero for the negative differential after deleting degree zero of the
Koszul chain complex. Source: Stacks, Tag 08CX
(blueprint: def-pc-shifted-koszul-augmentation).
Proof: the two minus signs cancel and `koszulBoundary_comp` gives zero. -/
theorem shiftedKoszul_square (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (n : ℕ) :
    (-ModuleCat.ofHom (ExteriorAlgebra.koszulBoundary A r f (n + 2))) ≫
      (-ModuleCat.ofHom (ExteriorAlgebra.koszulBoundary A r f (n + 1))) = 0 := by
  simpa only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg] using
    ExteriorAlgebra.koszulBoundary_comp A r f (n + 1)

/-- The chain version of `I`, with term `K_(n+1)` and negative differential.
Source: Stacks, Tag 08CX (blueprint: def-pc-shifted-koszul-augmentation). -/
def shiftedKoszulChain (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) :
    ChainComplex (ModuleCat.{u} A) ℕ :=
  ChainComplex.of (fun n ↦ (ExteriorAlgebra.koszulComplex A r f).X (n + 1))
    (fun n ↦ -ModuleCat.ofHom (ExteriorAlgebra.koszulBoundary A r f (n + 1)))
    (shiftedKoszul_square A r f)

/-- The cochain complex `I^i = K^(i-1)` for `i ≤ 0`, zero for `i > 0`,
with the negative Koszul differential. Source: Stacks, Tag 08CX
(blueprint: def-pc-shifted-koszul-augmentation). -/
def shiftedKoszulComplex (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  (shiftedKoszulChain A r f).extend ComplexShape.embeddingDownNat

/-- The augmentation's degree-zero component kills the preceding differential.
Source: Stacks, Tag 08CX (blueprint: def-pc-shifted-koszul-augmentation).
Proof: contraction squared is zero, and composition with the degree-zero
exterior-power identification preserves zero. The sign does not affect vanishing. -/
theorem shiftedKoszul_augmentation_comp (A : Type u) [CommRing A] (r : ℕ)
    (f : Fin r → A) :
    (shiftedKoszulChain A r f).d 1 0 ≫
      ModuleCat.ofHom ((exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap.comp
        (ExteriorAlgebra.koszulBoundary A r f 0)) = 0 := by
  change (-ModuleCat.ofHom (ExteriorAlgebra.koszulBoundary A r f 1)) ≫
    (ModuleCat.ofHom (ExteriorAlgebra.koszulBoundary A r f 0) ≫
      ModuleCat.ofHom (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap) = 0
  rw [Preadditive.neg_comp, ← Category.assoc,
    ExteriorAlgebra.koszulBoundary_comp, zero_comp, neg_zero]

/-- The canonical augmentation of the chain version of `I` to `A` in degree zero.
Its component in degree zero sends the standard basis vector `i` to `f i`.
Source: Stacks, Tag 08CX (blueprint: def-pc-shifted-koszul-augmentation). -/
def shiftedKoszulChainAugmentation (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) :
    shiftedKoszulChain A r f ⟶ (ChainComplex.single₀ (ModuleCat.{u} A)).obj
      (ModuleCat.of A A) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom ((exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap.comp
      (ExteriorAlgebra.koszulBoundary A r f 0)), shiftedKoszul_augmentation_comp A r f⟩

/-- The augmentation `I → A`, viewed as an integer-indexed cochain map.
Source: Stacks, Tag 08CX (blueprint: def-pc-shifted-koszul-augmentation). -/
def shiftedKoszulAugmentation (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) :
    shiftedKoszulComplex A r f ⟶
      ((ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)).extend
        ComplexShape.embeddingDownNat :=
  HomologicalComplex.extendMap (shiftedKoszulChainAugmentation A r f)
    ComplexShape.embeddingDownNat

/-- The derived augmentation, obtained by associated sheaves then localization.
Its source is `I` and its target is the structure sheaf in degree zero. Associated
sheaves are Mathlib's `tilde.functor` applied termwise, in the form of the landed
lem-pc-koszul-affine-detection and lemma-coherent-base-change-invertible-sheaves--1 citers.
Source: Stacks, Tag 08CX; Tag 01I6 (blueprint: def-pc-shifted-koszul-augmentation). -/
def affineKoszulAugmentation (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (r : ℕ) (f : Fin r → A) :
    DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
          (shiftedKoszulComplex A r f)) ⟶
      DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
          (((ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)).extend
            ComplexShape.embeddingDownNat)) :=
  DerivedCategory.Q.map
    ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      _ _ _ _ (tilde.functor (.of A))
      ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).map
      (shiftedKoszulAugmentation A r f))

end
end AlgebraicGeometry
