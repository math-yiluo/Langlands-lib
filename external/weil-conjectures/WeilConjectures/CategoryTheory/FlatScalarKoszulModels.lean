/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RestrictionDerivedProducts
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
/-! # Strict scalar Koszul models

These are the existing ordered-coordinate definitions for scalar comparison, separated
from the derived comparison so that the finite calculation can be used independently.
Source: Stacks Project, Tags 0A0E, 0913, 0A07 and 0941.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}

/-- The existing category of module sheaves. Source: Stacks 0A0E
(auxiliary; not a blueprint node). -/
abbrev Modules (O : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)

/-- Strict inverse towers in the existing module category. Source: Stacks 0941
(auxiliary; not a blueprint node). -/
abbrev Towers (O : Sheaf J CommRingCat.{u}) := ℕᵒᵖ ⥤ Modules O

/-- The tensor bifunctor already used by the Koszul system. Source: Stacks 0A0E
(auxiliary; not a blueprint node). -/
abbrev tensor (O : Sheaf J CommRingCat.{u}) :=
  @curriedTensor (Modules O) _ (SheafOfModules.monoidalCategory O)

/-- The rank-one module sheaf. Source: Stacks 0A0E
(auxiliary; not a blueprint node). -/
abbrev one (O : Sheaf J CommRingCat.{u}) :=
  SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)

/-- The number of selected factors, as an integer degree. Source: Stacks 0913
(auxiliary; not a blueprint node). -/
def degree : (r : ℕ) → (Fin r → Bool) → ℤ :=
  fun r ↦ Nat.rec (fun _ ↦ 0)
    (fun _ ih e ↦ (if e 0 then 1 else 0) + ih (fun i ↦ e i.succ)) r

/-- The basis inclusion in degree zero or one of a positive Koszul factor.
Source: Stacks 0913
(auxiliary; not a blueprint node). -/
def factorBasis (O : Sheaf J CommRingCat.{u})
    (a : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) (e : Bool) :
    one O ⟶ (ringedKoszulFactor O a m).X (if e then 1 else 0) :=
  match e with
  | false => (HomologicalComplex.doubleXIso₀ _ _).inv
  | true => (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv

/-- The ordered tensor basis inclusion into the positive Koszul complex.
Source: Stacks 0913; the empty tensor has its sole basis vector in degree zero.
(auxiliary; not a blueprint node). -/
def positiveBasis (O : Sheaf J CommRingCat.{u}) : (r : ℕ) →
    (a : Fin r → (O.obj ⋙ forget CommRingCat).sections) → (m : ℕ) →
    (e : Fin r → Bool) → one O ⟶ (ringedKoszulDiagram O r a).obj m |>.X (degree r e) :=
  letI : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  fun r ↦ Nat.rec
    (fun _ _ _ ↦ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one O)).inv)
    (fun r ih a m e ↦
      (λ_ (one O)).inv ≫
        ((tensor O).map (factorBasis O (a 0) m (e 0))).app _ ≫
        ((tensor O).obj _).map (ih (fun i ↦ a i.succ) m (fun i ↦ e i.succ)) ≫
        CochainComplex.ιMapBifunctor (ringedKoszulFactor O (a 0) m)
          ((ringedKoszulDiagram O r (fun i ↦ a i.succ)).obj m) (tensor O)
          (if e 0 then 1 else 0) (degree r (fun i ↦ e i.succ)) (degree (r + 1) e) rfl) r

/-- Evaluate the dual Koszul complex on a specified positive tensor basis vector.
It is zero outside the vector's dual degree. Source: Stacks 0A0E and 0913
(auxiliary; not a blueprint node). -/
def dualCoordinate (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (a : Fin r → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ)
    (e : Fin r → Bool) (q : ℤ) :
    ((ringedKoszulDualTower O r a).obj (op m)).X q ⟶ one O :=
  if h : degree r e + q = 0 then
    homComplexπ ((ringedKoszulDiagram O r a).obj m) (ringedSiteRingComplex O)
        q (degree r e) 0 h ≫
      SheafOfModules.homObjMap (R := O) (positiveBasis O r a m e)
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one O)).hom ≫
      (SheafOfModules.homObjUnitIso (R := O) (one O)).hom
  else 0

/-- The actual exterior-coordinate projection of a tensor-tower term.
The total complex uses coproducts, and this map is their universal descendent.
Source: Stacks 0A0E; the projection sends c tensor e_S to c.
(auxiliary; not a blueprint node). -/
def coordinate (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (a : Fin r → (O.obj ⋙ forget CommRingCat).sections) (N : ringedSiteComplex O)
    (m : ℕ) (e : Fin r → Bool) (n : ℤ) :
    ((ringedKoszulTensorTowerComplex O r a N).X n).obj (op m) ⟶
      N.X (n + degree r e) :=
  letI : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  HomologicalComplex.mapBifunctorDesc
    (K₁ := N) (K₂ := (ringedKoszulDualTower O r a).obj (op m))
    (F := tensor O) (c := .up ℤ) (fun p q _ ↦
      if hp : p = n + degree r e then
        ((tensor O).obj (N.X p)).map (dualCoordinate O r a m e q) ≫
          (ρ_ (N.X p)).hom ≫ eqToHom (congrArg N.X hp)
      else 0)

/-- Restriction of scalars, exactly Mathlib's ring-sheaf functor. Source: Stacks 0A07
(auxiliary; not a blueprint node). -/
abbrev restriction {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :=
  SheafOfModules.restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)

/-- Ordinary inverse limit on complexes of strict towers. Source: Stacks 0941
(auxiliary; not a blueprint node). -/
abbrev limitComplex (O : Sheaf J CommRingCat.{u}) :=
  (lim : Towers O ⥤ Modules O).mapHomologicalComplex (.up ℤ)

end CategoryTheory.FlatScalarKoszul
