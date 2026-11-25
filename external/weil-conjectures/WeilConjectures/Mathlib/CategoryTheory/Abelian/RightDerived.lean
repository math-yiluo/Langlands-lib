/-
Copyright (c) 2026 The Weil Conjectures Project Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Additivity of right derived functors

The right derived functors `F.rightDerived n` of an additive functor `F` are additive. This
follows from the additivity of `injectiveResolutions C`.

Natural endomorphisms of the identity functors which are intertwined by `F` are intertwined by
its right derived functors (`CategoryTheory.Functor.rightDerived_map_app_eq`).
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D] (F : C ⥤ D) [F.Additive]

instance : F.rightDerivedToHomotopyCategory.Additive :=
  inferInstanceAs (injectiveResolutions C ⋙ F.mapHomotopyCategory _).Additive

/-- The right derived functors of an additive functor are additive. -/
instance (n : ℕ) : (F.rightDerived n).Additive :=
  inferInstanceAs
    (F.rightDerivedToHomotopyCategory ⋙ HomotopyCategory.homologyFunctor D _ n).Additive

/-- Let `α` and `β` be natural endomorphisms of the identity functors of `C` and `D` which are
intertwined by `F`: `F (α M) = β (F M)`. Then they are intertwined by every right derived
functor of `F`: `R^n F (α M) = β (R^n F M)`. -/
theorem rightDerived_map_app_eq (α : 𝟭 C ⟶ 𝟭 C) (β : 𝟭 D ⟶ 𝟭 D)
    (h : ∀ M, F.map (α.app M) = β.app (F.obj M)) (n : ℕ) (M : C) :
    (F.rightDerived n).map (α.app M) = β.app ((F.rightDerived n).obj M) := by
  let P := injectiveResolution M
  let φ : P.cocomplex ⟶ P.cocomplex :=
    { f i := α.app (P.cocomplex.X i)
      comm' i j _ := (α.naturality (P.cocomplex.d i j)).symm }
  have w : P.ι ≫ φ = (CochainComplex.single₀ C).map (α.app M) ≫ P.ι := by
    ext
    simpa [φ] using α.naturality (P.ι.f 0)
  rw [F.rightDerived_map_eq n (α.app M) φ w]
  have hφ := HomologicalComplex.homologyMap_eq_app_homology β ((F.mapHomologicalComplex _).map φ)
    (fun i ↦ h _) n
  rw [Functor.comp_map, HomologicalComplex.homologyFunctor_map, hφ]
  rw [← Category.assoc, Iso.comp_inv_eq]
  exact β.naturality (P.isoRightDerivedObj F n).hom

end CategoryTheory.Functor
