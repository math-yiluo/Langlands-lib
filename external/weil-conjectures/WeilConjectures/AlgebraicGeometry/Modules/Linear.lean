/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-!
# Modules over a scheme over a field form a linear category

For a scheme `X` over `Spec k`, the category `X.Modules` is `k`-linear: `c • φ` is `φ` followed
by multiplication by the image of `c` in `Γ(X, ⊤)`
(`AlgebraicGeometry.Scheme.Modules.linearOfOver`). In particular the groups `Ext M N n` are
`k`-vector spaces (`CategoryTheory.Abelian.Ext`'s instance for linear categories).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The `k`-module structure on morphisms of `𝒪_X`-modules, for a `k`-scheme `X`: `c • φ` is `φ`
followed by multiplication by the image of `c` in `Γ(X, ⊤)`. -/
noncomputable instance homModuleOfOver (M N : X.Modules) : Module k (M ⟶ N) where
  smul c φ := φ ≫ N.smulHom (globalSectionsRingHom k c)
  one_smul φ := by
    change φ ≫ N.smulHom (globalSectionsRingHom k 1) = φ
    rw [map_one, smulHom_one, Category.comp_id]
  mul_smul a b φ := by
    change φ ≫ N.smulHom (globalSectionsRingHom k (a * b)) =
      (φ ≫ N.smulHom (globalSectionsRingHom k b)) ≫ N.smulHom (globalSectionsRingHom k a)
    rw [map_mul, smulHom_mul, Category.assoc]
  smul_zero c := Limits.zero_comp
  smul_add c φ ψ := Preadditive.add_comp _ _ _ _ _ _
  add_smul a b φ := by
    change φ ≫ N.smulHom (globalSectionsRingHom k (a + b)) =
      φ ≫ N.smulHom (globalSectionsRingHom k a) + φ ≫ N.smulHom (globalSectionsRingHom k b)
    rw [map_add, smulHom_add, Preadditive.comp_add]
  zero_smul φ := by
    change φ ≫ N.smulHom (globalSectionsRingHom k 0) = 0
    rw [map_zero, smulHom_zero, Limits.comp_zero]

/-- `c • φ` is `φ` followed by multiplication by `c`. -/
lemma smul_hom_eq {M N : X.Modules} (c : k) (φ : M ⟶ N) :
    c • φ = φ ≫ N.smulHom (globalSectionsRingHom k c) :=
  rfl

/-- **`X.Modules` is a `k`-linear category** for a `k`-scheme `X`. -/
noncomputable instance linearOfOver : Linear k X.Modules where
  homModule := homModuleOfOver k
  smul_comp M N P c f g := by
    rw [smul_hom_eq, smul_hom_eq, Category.assoc, Category.assoc, smulHom_naturality]
  comp_smul M N P f c g := by
    rw [smul_hom_eq, smul_hom_eq, Category.assoc]

/-- The map induced on cohomology by `c • φ` is `c` times the map induced by `φ`. -/
lemma H.map_smul_hom {M N : X.Modules} (c : k) (φ : M ⟶ N) (n : ℕ) (x : M.H n) :
    H.map (c • φ) n x = c • H.map φ n x :=
  H.map_comp_apply _ _ n x

end AlgebraicGeometry.Scheme.Modules
