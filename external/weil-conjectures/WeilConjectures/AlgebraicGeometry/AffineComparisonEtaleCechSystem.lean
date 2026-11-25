/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Simultaneous affine étale presentations of a finite Čech nerve

Source: Stacks Project, Tags 099U, 099T, 01ZM, 01ZN and 07RP.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Geometric presentation data, independent of a coefficient sheaf or cocycle.
The transition maps and cone legs respect every repeated-intersection projection.
Source: Stacks Project, Tag 099U, finite Čech approximations.
(auxiliary; not a blueprint node). -/
structure AffineEtaleCechSystem (Y : Scheme.{u}) (V : Y.ProEt)
    {n : ℕ} (U : Fin n → Over V) (I : Type u) [SmallCategory I] where
  W : I → Y.Etale
  T : I → Fin n → Y.Etale
  f : ∀ i a, T i a ⟶ W i
  covering : ∀ i, Sieve.ofArrows (T i) (f i) ∈ Y.smallEtaleTopology (W i)
  trans : ∀ {i j : I} (_a : i ⟶ j) (k : ℕ) (y : Fin (k + 1) → Fin n),
    (Presheaf.cechNerveObj (fun b ↦ Over.mk (f i b)) y).left ⟶
      (Presheaf.cechNerveObj (fun b ↦ Over.mk (f j b)) y).left
  trans_id : ∀ i k y, trans (𝟙 i) k y = 𝟙 _
  trans_comp : ∀ {i j l : I} (a : i ⟶ j) (b : j ⟶ l) k y,
    trans (a ≫ b) k y = trans a k y ≫ trans b k y
  trans_face : ∀ {i j : I} (a : i ⟶ j) (k m : ℕ)
      (y : Fin (m + 1) → Fin n) (θ : Fin (k + 1) → Fin (m + 1)),
    trans a m y ≫ (Presheaf.cechNerveMap (fun b ↦ Over.mk (f j b)) y θ).left =
      (Presheaf.cechNerveMap (fun b ↦ Over.mk (f i b)) y θ).left ≫
        trans a k (y ∘ θ)
  π : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n) (i : I),
    (Presheaf.cechNerveObj U y).left ⟶ (Scheme.toProEt Y).obj
      (Presheaf.cechNerveObj (fun b ↦ Over.mk (f i b)) y).left
  π_naturality : ∀ {i j : I} (a : i ⟶ j) k y,
    π k y i ≫ (Scheme.toProEt Y).map (trans a k y) = π k y j
  π_face : ∀ (i : I) (k m : ℕ) (y : Fin (m + 1) → Fin n)
      (θ : Fin (k + 1) → Fin (m + 1)),
    (Presheaf.cechNerveMap U y θ).left ≫ π k (y ∘ θ) i =
      π m y i ≫ (Scheme.toProEt Y).map
        (Presheaf.cechNerveMap (fun b ↦ Over.mk (f i b)) y θ).left
  affine : ∀ (i : I) (k : ℕ) (y : Fin (k + 1) → Fin n),
    IsAffine (Presheaf.cechNerveObj (fun b ↦ Over.mk (f i b)) y).left.left

namespace AffineEtaleCechSystem

variable {Y : Scheme.{u}} {V : Y.ProEt} {n : ℕ} {U : Fin n → Over V}
  {I : Type u} [SmallCategory I] (S : AffineEtaleCechSystem Y V U I)

/-- The presentation diagram of a fixed repeated intersection. -/
noncomputable def nerve (k : ℕ) (y : Fin (k + 1) → Fin n) : I ⥤ Y.Etale where
  obj i := (Presheaf.cechNerveObj (fun b ↦ Over.mk (S.f i b)) y).left
  map a := S.trans a k y
  map_id i := S.trans_id i k y
  map_comp a b := S.trans_comp a b k y

/-- The cone from the original intersection to its étale approximations. -/
noncomputable def nerveCone (k : ℕ) (y : Fin (k + 1) → Fin n) :
    Cone (S.nerve k y ⋙ Scheme.toProEt Y) where
  pt := (Presheaf.cechNerveObj U y).left
  π.app i := S.π k y i
  π.naturality i j a := by
    change 𝟙 _ ≫ S.π k y j = S.π k y i ≫ (Scheme.toProEt Y).map (S.trans a k y)
    rw [Category.id_comp]
    exact (S.π_naturality a k y).symm

end AffineEtaleCechSystem

end AlgebraicGeometry.ProEtale
