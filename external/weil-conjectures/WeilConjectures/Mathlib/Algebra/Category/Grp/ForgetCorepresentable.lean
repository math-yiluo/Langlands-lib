/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# `ℤ` is a projective abelian group

The forgetful functor `AddCommGrpCat ⥤ Type` is corepresented by `ℤ`, and it maps epimorphisms
to surjections; hence `ℤ` is a projective object of `AddCommGrpCat`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AddCommGrpCat

/-- The group `ℤ` is a projective object of `AddCommGrpCat`: a morphism out of `ℤ` is determined
by the image of `1`, which lifts along any surjection. -/
instance projective_of_uliftInt : Projective (of (ULift.{u} ℤ)) where
  factors {E X} f e he := by
    obtain ⟨a, ha⟩ := (epi_iff_surjective e).1 he (f (ULift.up 1))
    refine ⟨ofHom ((zmultiplesHom E a).comp AddEquiv.ulift.toAddMonoidHom), ?_⟩
    ext ⟨n⟩
    change e (n • a) = f ⟨n⟩
    rw [map_zsmul, ha, ← map_zsmul]
    congr 1
    ext
    simp

end AddCommGrpCat
