/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

/-! # Explicit shifted quotient systems

Source: Stacks Project, Lemma 087X, claims (b)--(c).
(blueprint: lem-weil-pbc-formal-shifted-quotient).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry
noncomputable section

/-- The explicit system with level n equal to S_(n+d)/I^(n+1) S_(n+d).
Source: Stacks Project, Lemma 087X, claim (b).
(blueprint: lem-weil-pbc-formal-shifted-quotient). -/
def formalShiftedQuotient {X : Scheme.{u}} (I : X.IdealSheafData)
    (S : ℕᵒᵖ ⥤ X.Modules) (d : ℕ) : ℕᵒᵖ ⥤ X.Modules where
  obj n := formalModuleQuotient I (n.unop + 1) (S.obj (op (n.unop + d)))
  map f := formalModuleQuotientMap I
    (S.map (homOfLE (Nat.add_le_add_right (leOfHom f.unop) d)).op)
    (Nat.succ_le_succ (leOfHom f.unop))
  map_id n := by
    have h : (homOfLE (Nat.add_le_add_right (leOfHom (𝟙 n).unop) d)).op =
        𝟙 (op (n.unop + d)) := Subsingleton.elim _ _
    rw [h, S.map_id]
    exact formalModuleQuotientMap_id I _ _
  map_comp f g := by
    rw [← formalModuleQuotientMap_comp, ← S.map_comp]
    congr 2

/-- Ideal multiplication vanishes after mapping to the annihilated target level.
Proof: multiplication factors through the target ideal product, which is zero.
Source: Stacks Project, Lemma 087X, claim (c).
(blueprint: lem-weil-pbc-formal-shifted-quotient). -/
theorem shiftedQuotient_kill {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I)
    (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj) (d n : ℕ) :
    Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι (n + 1)).2
        (S.obj (op (n + d))) ≫
      (j.app (op (n + d)) ≫ F.obj.map (homOfLE (Nat.le_add_right n d)).op) = 0 := by
  obtain ⟨k, hk⟩ := formalModuleQuotient_factor I
    (j.app (op (n + d)) ≫ F.obj.map (homOfLE (Nat.le_add_right n d)).op)
    (Nat.le_refl (n + 1))
  rw [hk, (F.property.2.1 n).eq_zero_of_src
    (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι (n + 1)).2
      (F.obj.obj (op n))), comp_zero]

/-- The descended inclusion, constructed by the cokernel universal property.
Source: Stacks Project, Lemma 087X, the map from the system of claim (c) to F.
(blueprint: lem-weil-pbc-formal-shifted-quotient). -/
def formalShiftedQuotientι {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I)
    (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj) (d : ℕ) :
    formalShiftedQuotient I S d ⟶ F.obj where
  app n := cokernel.desc _
    (j.app (op (n.unop + d)) ≫ F.obj.map (homOfLE (Nat.le_add_right n.unop d)).op)
    (shiftedQuotient_kill I F S j d n.unop)
  naturality {a b} f := by
    have : Epi (formalModuleQuotientπ I (a.unop + 1)
        (S.obj (op (a.unop + d)))) := by
      dsimp only [formalModuleQuotientπ]
      infer_instance
    apply (cancel_epi (formalModuleQuotientπ I (a.unop + 1)
      (S.obj (op (a.unop + d))))).1
    dsimp [formalShiftedQuotient]
    simp only [formalModuleQuotientπ, formalModuleQuotientMap,
      Category.assoc, cokernel.π_desc_assoc, cokernel.π_desc]
    rw [← Category.assoc, j.naturality, Category.assoc, ← F.obj.map_comp,
      ← F.obj.map_comp]
    congr 1

/-- The defining equation of the descended inclusion.
Proof: this is the factorization equation for cokernel.desc.
Source: Stacks Project, Lemma 087X, claim (c).
(blueprint: lem-weil-pbc-formal-shifted-quotient). -/
theorem formalShiftedQuotientι_comp {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I)
    (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj) (d n : ℕ) :
    formalModuleQuotientπ I (n + 1) (S.obj (op (n + d))) ≫
      (formalShiftedQuotientι I F S j d).app (op n) =
    j.app (op (n + d)) ≫ F.obj.map (homOfLE (Nat.le_add_right n d)).op := by
  exact cokernel.π_desc _ _ _

end
end AlgebraicGeometry
