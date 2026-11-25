/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Exact comparison of derived cokernel adjunctions

The comparison is the inverse of the mate of the exact right-adjoint square.
Multiplication short exact sequences show that the target universal counit computes
on the image of a resolving object. No preservation of the resolving class is needed.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
section
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [I.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
private theorem square_factors (e : F ⋙ G ≅ H ⋙ I) (K : CochainComplex A ℤ) :
    (CategoryTheory.Functor.mapDerivedCategorySquareIso e).hom.app
        (DerivedCategory.Q.obj K) ≫
      I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
      I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := by
  simp only [CategoryTheory.Functor.mapDerivedCategorySquareIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_factors,
    CategoryTheory.Functor.mapDerivedCategoryNatIso_fac]
  rw [← CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_factors F G K]
  erw [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact Category.assoc _ _ _
end
section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (E : A ⥤ B) (E' : A' ⥤ B') [E.Additive] [E'.Additive]
  (R : B ⥤ A) (R' : B' ⥤ A') [R.Additive] [R'.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  (a : E ⊣ R) (a' : E' ⊣ R')
  (L : DerivedCategory A ⥤ DerivedCategory B)
  (L' : DerivedCategory A' ⥤ DerivedCategory B')
  (ad : L ⊣ R.mapDerivedCategory) (ad' : L' ⊣ R'.mapDerivedCategory)
  (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (ε' : DerivedCategory.Q ⋙ L' ⟶ E'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (F : A ⥤ A') (G : B ⥤ B') [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (ρ : R ⋙ F ≅ G ⋙ R') (e : E ⋙ G ≅ F ⋙ E')
  (β : F.mapDerivedCategory ⋙ L' ⟶ L ⋙ G.mapDerivedCategory)
  (hβ : ∀ X, ad'.unit.app (F.mapDerivedCategory.obj X) ≫
    R'.mapDerivedCategory.map (β.app X) =
    F.mapDerivedCategory.map (ad.unit.app X) ≫
      (CategoryTheory.Functor.mapDerivedCategorySquareIso ρ).hom.app (L.obj X))
  (hunit : ∀ P, ad.unit.app (DerivedCategory.Q.obj P) ≫
    R.mapDerivedCategory.map (ε.app P) ≫
    R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P))
  (hunit' : ∀ P, ad'.unit.app (DerivedCategory.Q.obj P) ≫
    R'.mapDerivedCategory.map (ε'.app P) ≫
    R'.mapDerivedCategoryFactors.hom.app ((E'.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a'.mapHomologicalComplex (.up ℤ)).unit.app P))
  (he : ∀ X, F.map (a.unit.app X) ≫ ρ.hom.app (E.obj X) ≫
    R'.map (e.hom.app X) = a'.unit.app (F.obj X))
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
  (a : L ⊣ R) (a' : L' ⊣ R') (F : A ⥤ A') (G : B ⥤ B')
  (ρ : R ⋙ F ≅ G ⋙ R')
variable [HasShift A ℤ] [HasShift B ℤ] [HasShift A' ℤ] [HasShift B' ℤ]
  [L.CommShift ℤ] [R.CommShift ℤ] [L'.CommShift ℤ] [R'.CommShift ℤ]
  [a.CommShift ℤ] [a'.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
  [NatTrans.CommShift ρ.hom ℤ]
end

section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (E : A ⥤ B) (E' : A' ⥤ B') [E.Additive] [E'.Additive]
  (R : B ⥤ A) (R' : B' ⥤ A') [R.Additive] [R'.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  (a : E ⊣ R) (a' : E' ⊣ R')
  (L : DerivedCategory A ⥤ DerivedCategory B)
  (L' : DerivedCategory A' ⥤ DerivedCategory B')
  [L.CommShift ℤ] [L'.CommShift ℤ]
  (ad : L ⊣ R.mapDerivedCategory) (ad' : L' ⊣ R'.mapDerivedCategory)
  [ad.CommShift ℤ] [ad'.CommShift ℤ]
  (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (ε' : DerivedCategory.Q ⋙ L' ⟶ E'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (F : A ⥤ A') (G : B ⥤ B') [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (ρ : R ⋙ F ≅ G ⋙ R') (e : E ⋙ G ≅ F ⋙ E')
  (hunit : ∀ P, ad.unit.app (DerivedCategory.Q.obj P) ≫
    R.mapDerivedCategory.map (ε.app P) ≫
    R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P))
  (hunit' : ∀ P, ad'.unit.app (DerivedCategory.Q.obj P) ≫
    R'.mapDerivedCategory.map (ε'.app P) ≫
    R'.mapDerivedCategoryFactors.hom.app ((E'.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a'.mapHomologicalComplex (.up ℤ)).unit.app P))
  (he : ∀ X, F.map (a.unit.app X) ≫ ρ.hom.app (E.obj X) ≫
    R'.map (e.hom.app X) = a'.unit.app (F.obj X))
  (H : CochainComplex A ℤ → Prop)
  (hres : ∀ K, ∃ (P : CochainComplex A ℤ) (p : P ⟶ K), H P ∧ QuasiIso p)
  (hcomp : ∀ P, H P → IsIso (ε.app P) ∧
    IsIso (ε'.app ((F.mapHomologicalComplex (.up ℤ)).obj P)))
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian A'] (n : ℕ)
  (E : A ⥤ B) (R : B ⥤ A) (E' : A' ⥤ B') (R' : B' ⥤ A') [R'.Full] [R'.Faithful]
  (a : E ⊣ R) (a' : E' ⊣ R')
  (hz : ∀ X : A, (n • 𝟙 X) ≫ a.unit.app X = 0)
  (hz' : ∀ X : A', (n • 𝟙 X) ≫ a'.unit.app X = 0)
  (hc : ∀ X : A, IsColimit (CokernelCofork.ofπ (a.unit.app X) (hz X)))
  (hc' : ∀ X : A', IsColimit (CokernelCofork.ofπ (a'.unit.app X) (hz' X)))
  (F : A ⥤ A') [F.Additive] [PreservesFiniteColimits F] (G : B ⥤ B')
  (ρ : R ⋙ F ≅ G ⋙ R')

include n hz hc hc' in
private theorem ordinary_exchange :
    ∃ e : E ⋙ G ≅ F ⋙ E', ∀ X : A,
      F.map (a.unit.app X) ≫ ρ.hom.app (E.obj X) ≫ R'.map (e.hom.app X) =
        a'.unit.app (F.obj X) := by
  classical
  let u (X : A) := F.map (a.unit.app X) ≫ ρ.hom.app (E.obj X)
  let b (X : A) := (a'.homEquiv (F.obj X) (G.obj (E.obj X))).symm (u X)
  have hb (X : A) : a'.unit.app (F.obj X) ≫ R'.map (b X) = u X := by
    exact (Adjunction.homEquiv_unit a' _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have hzero (X : A) : (n • 𝟙 (F.obj X)) ≫ F.map (a.unit.app X) = 0 := by
    rw [← F.map_id, ← F.map_nsmul, ← F.map_comp, hz, F.map_zero]
  have hzero' (X : A) : (n • 𝟙 (F.obj X)) ≫ u X = 0 := by
    dsimp only [u]
    rw [← Category.assoc, hzero, zero_comp]
  have hU (X : A) : IsColimit (CokernelCofork.ofπ (u X) (hzero' X)) := by
    have hFm : IsColimit (CokernelCofork.ofπ (F.map (a.unit.app X)) (hzero X)) := by
      let h := isColimitCoforkMapOfIsColimit' F (hz X) (hc X)
      exact CokernelCofork.isColimitOfIsColimitOfIff' h (n • 𝟙 (F.obj X)) (by
        intro Z k
        simp only [F.map_nsmul, F.map_id])
    exact IsColimit.ofIsoColimit hFm (Cofork.ext (ρ.app (E.obj X)) rfl)
  have hiso (X : A) : IsIso (b X) := by
    have hepi : Epi (a'.unit.app (F.obj X)) := Cofork.IsColimit.epi (hc' (F.obj X))
    let e := (hc' (F.obj X)).coconePointUniqueUpToIso (hU X)
    have he : a'.unit.app (F.obj X) ≫ e.hom = u X :=
      (hc' (F.obj X)).comp_coconePointUniqueUpToIso_hom (hU X) WalkingParallelPair.one
    have heq : R'.map (b X) = e.hom := (cancel_epi (a'.unit.app (F.obj X))).1
      ((hb X).trans he.symm)
    have : IsIso (R'.map (b X)) := by rw [heq]; infer_instance
    exact isIso_of_reflects_iso (b X) R'
  let β : F ⋙ E' ⟶ E ⋙ G :=
    { app := b
      naturality := by
        intro X Y f
        apply (a'.homEquiv (F.obj X) (G.obj (E.obj Y))).injective
        rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
        simp only [R'.map_comp, ← Category.assoc]
        erw [← a'.unit.naturality (F.map f), Category.assoc, hb, hb]
        dsimp only [u]
        simp only [Category.assoc, CategoryTheory.Functor.id_map]
        rw [← F.map_comp_assoc]
        erw [a.unit.naturality f, F.map_comp]
        simp only [Category.assoc]
        exact congrArg (fun z ↦ F.map (a.unit.app X) ≫ z)
          (ρ.hom.naturality (E.map f)) }
  let e := (NatIso.ofComponents (fun X ↦ asIso (β.app X))
    (fun f ↦ β.naturality f)).symm
  refine ⟨e, ?_⟩
  intro X
  rw [← Category.assoc]
  change u X ≫ R'.map (inv (b X)) = _
  rw [← hb, Category.assoc, ← R'.map_comp, IsIso.hom_inv_id, R'.map_id]
  erw [Category.comp_id]


end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
section
variable {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* B] [Abelian B] [HasDerivedCategory B]
  (E : A ⥤ B) [E.Additive] (R : B ⥤ A) [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (a : E ⊣ R) (L : DerivedCategory A ⥤ DerivedCategory B) (ad : L ⊣ R.mapDerivedCategory)
  (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (H : CochainComplex A ℤ → Prop)
  (hres : ∀ K : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (p : P ⟶ K),
    H P ∧ QuasiIso p)
  (hunit : ∀ P, H P → ad.unit.app (DerivedCategory.Q.obj P) ≫
    R.mapDerivedCategory.map (ε.app P) ≫
    R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P))
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
section
variable {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* B] [Abelian B] [HasDerivedCategory B]
  (n : ℕ) (E : A ⥤ B) [E.Additive] (R : B ⥤ A) [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (a : E ⊣ R)
  (hz : ∀ X : A, (n • 𝟙 X) ≫ a.unit.app X = 0)
  (hc : ∀ X : A, IsColimit (CokernelCofork.ofπ (a.unit.app X) (hz X)))
variable (L : DerivedCategory A ⥤ DerivedCategory B)
  (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  [R.ReflectsIsomorphisms]
end

section CokernelExchange
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (n : ℕ) (E : A ⥤ B) (E' : A' ⥤ B') [E.Additive] [E'.Additive]
  (R : B ⥤ A) (R' : B' ⥤ A') [R.Additive] [R'.Additive] [R'.Full] [R'.Faithful]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  (a : E ⊣ R) (a' : E' ⊣ R')
  (L : DerivedCategory A ⥤ DerivedCategory B)
  (L' : DerivedCategory A' ⥤ DerivedCategory B')
  [L.CommShift ℤ] [L'.CommShift ℤ]
  (ad : L ⊣ R.mapDerivedCategory) (ad' : L' ⊣ R'.mapDerivedCategory)
  [ad.CommShift ℤ] [ad'.CommShift ℤ]
  (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (ε' : DerivedCategory.Q ⋙ L' ⟶ E'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (F : A ⥤ A') (G : B ⥤ B') [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (ρ : R ⋙ F ≅ G ⋙ R')
  (hz : ∀ X : A, (n • 𝟙 X) ≫ a.unit.app X = 0)
  (hz' : ∀ X : A', (n • 𝟙 X) ≫ a'.unit.app X = 0)
  (hc : ∀ X : A, IsColimit (CokernelCofork.ofπ (a.unit.app X) (hz X)))
  (hc' : ∀ X : A', IsColimit (CokernelCofork.ofπ (a'.unit.app X) (hz' X)))
  (H : CochainComplex A ℤ → Prop) (H' : CochainComplex A' ℤ → Prop)
  (hres : ∀ K, ∃ (P : CochainComplex A ℤ) (p : P ⟶ K), H P ∧ QuasiIso p)
  (hres' : ∀ K, ∃ (P : CochainComplex A' ℤ) (p : P ⟶ K), H' P ∧ QuasiIso p)
  (hm : ∀ P, H P → ∀ i : ℤ, Mono (n • 𝟙 (P.X i)))
  (hm' : ∀ P, H' P → ∀ i : ℤ, Mono (n • 𝟙 (P.X i)))
  (hcomp : ∀ P, H P → IsIso (ε.app P))
  (hcomp' : ∀ P, H' P → IsIso (ε'.app P))
  (hu : ∀ P, H P → ad.unit.app (DerivedCategory.Q.obj P) ≫
    R.mapDerivedCategory.map (ε.app P) ≫
    R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P))
  (hu' : ∀ P, H' P → ad'.unit.app (DerivedCategory.Q.obj P) ≫
    R'.mapDerivedCategory.map (ε'.app P) ≫
    R'.mapDerivedCategoryFactors.hom.app ((E'.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a'.mapHomologicalComplex (.up ℤ)).unit.app P))

end CokernelExchange
