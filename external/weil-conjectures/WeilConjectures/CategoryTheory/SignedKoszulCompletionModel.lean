/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.CategoryTheory.RingedKoszulSystem

/-!
# The explicit signed Koszul completion model

Source: Stacks Project, algebraization.tex, Tag 0A0E, and the finite-coordinate calculation
in lem-cbc-exact-linear-koszul-fiber (auxiliary; not a blueprint node).

The negative Koszul factors are actual two-term complexes and their ordered tensor uses
`ringedKoszulTensor`, hence `CochainComplex.mapBifunctor` and its total-tensor signs.
The model structure records products by their universal property and the fibre by its
specified two coordinates. No object is selected from an unspecified existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v w z

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace CategoryTheory

/-- The negative Koszul factor in degrees -1 and 0, at exponent m+1.
Source: Stacks Tag 0A0E (auxiliary; not a blueprint node). -/
def ringedNegativeKoszulFactor {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u})
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) : ringedSiteComplex O :=
  HomologicalComplex.double (((ringedKoszulScalar O b) ^ (m + 1)).asHom)
    (by decide : (ComplexShape.up ℤ).Rel (-1) 0)

/-- The ordered tensor of negative factors; the empty tensor is O[0].
Source: Stacks Tag 0A0E (auxiliary; not a blueprint node). -/
def ringedNegativeKoszul {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u}) :
    (r : ℕ) → (Fin r → (O.obj ⋙ forget CommRingCat).sections) →
      ℕ → ringedSiteComplex O :=
  fun r ↦ Nat.rec
    (fun _ _ ↦ ringedSiteRingComplex O)
    (fun _ ih b m ↦ ((ringedKoszulTensor O).obj
      (ringedNegativeKoszulFactor O (b 0) m)).obj (ih (fun i ↦ b i.succ) m)) r

/-- Tensoring a complex with the ordered negative Koszul complex at exponent m+1.
Source: Stacks Tag 0A0E (auxiliary; not a blueprint node). -/
def ringedNegativeKoszulTensor {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u})
    {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    {r : ℕ} (a : Fin r → A) (m : ℕ) : ringedSiteComplex O ⥤ ringedSiteComplex O :=
  (ringedKoszulTensor O).flip.obj
    (ringedNegativeKoszul O r (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m)

/-- A one in a specified degree of the negative two-term factor, zero off its support.
Source: Stacks Tag 0A0E (auxiliary; not a blueprint node). -/
def ringedNegativeKoszulFactorBasis {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u})
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) (n : ℤ) :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶
      (ringedNegativeKoszulFactor O b m).X n :=
  if h : n = -1 then
    (HomologicalComplex.doubleXIso₀ _ _).inv ≫
      eqToHom (congrArg (ringedNegativeKoszulFactor O b m).X h.symm)
  else if h : n = 0 then
    (HomologicalComplex.doubleXIso₁ _ _ (by decide : (-1 : ℤ) ≠ 0)).inv ≫
      eqToHom (congrArg (ringedNegativeKoszulFactor O b m).X h.symm)
  else 0

/-- The pure tensor with entries one, in the ordered subset coordinate of Q.
The recursion uses the canonical tensor inclusions and the inverse unitor, with no sign
change. The off-degree entries are zero.
Source: Stacks Tag 0A0E (auxiliary; not a blueprint node). -/
def ringedNegativeKoszulBasis {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u}) :
    (r : ℕ) → (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) →
      (m : ℕ) → (I : Finset (Fin r)) → (n : ℤ) →
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶
        (ringedNegativeKoszul O r b m).X n :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  fun r ↦ Nat.rec
    (fun _ _ _ n ↦ if h : n = 0 then
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv ≫
        eqToHom (congrArg (ringedSiteRingComplex O).X h.symm) else 0)
    (fun k ih b m I n ↦
      (MonoidalCategory.leftUnitor
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).inv ≫
      (MonoidalCategory.tensorHom
        (ringedNegativeKoszulFactorBasis O (b 0) m
          (if (0 : Fin (k + 1)) ∈ I then -1 else 0))
        (ih (fun i ↦ b i.succ) m
          (I.preimage Fin.succ (fun _ _ _ _ h ↦ Fin.succ_injective k h))
          (n - if (0 : Fin (k + 1)) ∈ I then -1 else 0))) ≫
      CochainComplex.ιMapBifunctor
        (ringedNegativeKoszulFactor O (b 0) m)
        (ringedNegativeKoszul O k (fun i ↦ b i.succ) m)
        (MonoidalCategory.curriedTensor _) (if (0 : Fin (k + 1)) ∈ I then -1 else 0)
        (n - if (0 : Fin (k + 1)) ∈ I then -1 else 0) n (by omega)) r

/-- The canonical inclusion z ↦ z tensor e_I into the total tensor, where every
factor of e_I is one. This fixes the finite-coordinate normalization, including I empty.
Source: Stacks Tag 0A0E (auxiliary; not a blueprint node). -/
def ringedNegativeKoszulSummand {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u})
    {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    {r : ℕ} (a : Fin r → A) (m : ℕ) (K : ringedSiteComplex O)
    (q : ℤ) (I : Finset (Fin r)) :
    K.X (q + I.card) ⟶ ((ringedNegativeKoszulTensor O ρ a m).obj K).X q :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  (MonoidalCategory.rightUnitor (K.X (q + I.card))).inv ≫
    MonoidalCategory.tensorHom (𝟙 _) (ringedNegativeKoszulBasis O r
      (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m I (-(I.card : ℤ))) ≫
    CochainComplex.ιMapBifunctor K
      (ringedNegativeKoszul O r (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m)
      (MonoidalCategory.curriedTensor _) (q + I.card) (-(I.card : ℤ)) q (by omega)

/-- The existing global-section Hom scalar action, restricted along the coefficient map.
This transparent wrapper supplies the recorded Hom-module instance explicitly.
Source: Stacks Tags 03DD, 04TT (auxiliary; not a blueprint node). -/
def ringedKoszulCoefficientSMul {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u})
    {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    {M N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)}
    (b : A) (f : M ⟶ N) : M ⟶ N :=
  letI := SheafOfModules.homModule O.obj
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).property M N
  (ρ b) • f

end CategoryTheory
