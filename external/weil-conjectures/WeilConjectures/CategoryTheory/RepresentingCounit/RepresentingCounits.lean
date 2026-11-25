/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Right adjoints constructed from representing counits

Source: current blueprint proposition-sp-tower-geometric, Charts and gluing: construct
functoriality from representing pairs, without a functorial choice of cones.
(blueprint: lem-sp-representing-counits-adjunction)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u₁ v₁ u₂ v₂
open CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A specified object and counit representing `Hom(F(-), Y)`.
Source: blueprint proposition-sp-tower-geometric, Charts and gluing.
(blueprint: lem-sp-representing-counits-adjunction) -/
structure RepresentingCounit (F : C ⥤ D) (Y : D) where
  object : C
  counit : F.obj object ⟶ Y
  bijective : ∀ X : C, Function.Bijective (fun f : X ⟶ object ↦ F.map f ≫ counit)

namespace RepresentingCounit

variable {F : C ⥤ D} {Y : D} (P : RepresentingCounit F Y)

/-- The representing bijection, in the orientation of an adjunction.
Source: blueprint proposition-sp-tower-geometric, Charts and gluing.
(blueprint: lem-sp-representing-counits-adjunction) -/
def homEquiv (X : C) : (F.obj X ⟶ Y) ≃ (X ⟶ P.object) :=
  (Equiv.ofBijective _ (P.bijective X)).symm

@[simp] theorem homEquiv_symm_apply (X : C) (f : X ⟶ P.object) :
    (P.homEquiv X).symm f = F.map f ≫ P.counit := rfl

@[simp] theorem map_homEquiv_counit (X : C) (f : F.obj X ⟶ Y) :
    F.map (P.homEquiv X f) ≫ P.counit = f :=
  (P.homEquiv X).symm_apply_apply f

/-- Naturality in the test object follows from associativity and functoriality.
Source: blueprint proposition-sp-tower-geometric, Charts and gluing.
(blueprint: lem-sp-representing-counits-adjunction) -/
theorem homEquiv_naturality {X X' : C} (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    P.homEquiv X' (F.map f ≫ g) = f ≫ P.homEquiv X g := by
  apply (P.homEquiv X').symm.injective
  simp only [Equiv.symm_apply_apply, homEquiv_symm_apply, F.map_comp, Category.assoc,
    map_homEquiv_counit]

/-- Representing pairs are uniquely isomorphic by the equation on their counits.
Source: blueprint proposition-sp-tower-geometric, Charts and gluing, uniqueness sentence.
Proof: transpose each counit by the other representing bijection. Injectivity proves
both inverse identities and uniqueness of the counit-preserving isomorphism.
(blueprint: lem-sp-representing-counits-adjunction) -/
theorem unique_iso (Q : RepresentingCounit F Y) :
    ∃! e : P.object ≅ Q.object, F.map e.hom ≫ Q.counit = P.counit := by
  obtain ⟨a, ha⟩ := (Q.bijective P.object).2 P.counit
  obtain ⟨b, hb⟩ := (P.bijective Q.object).2 Q.counit
  have hab : a ≫ b = 𝟙 _ := by
    apply (P.bijective P.object).1
    simp only [F.map_comp, Category.assoc, hb, ha, F.map_id, Category.id_comp]
  have hba : b ≫ a = 𝟙 _ := by
    apply (Q.bijective Q.object).1
    simp only [F.map_comp, Category.assoc, ha, hb, F.map_id, Category.id_comp]
  refine ⟨⟨a, b, hab, hba⟩, ha, ?_⟩
  intro e he
  apply Iso.ext
  exact (Q.bijective P.object).1 (he.trans ha.symm)

end RepresentingCounit

variable {F : C ⥤ D} (P : ∀ Y : D, RepresentingCounit F Y)

/-- The map of the right adjoint is the unique transpose of the composed counit.
Source: blueprint proposition-sp-tower-geometric, Charts and gluing.
(blueprint: lem-sp-representing-counits-adjunction) -/
def representingCounitRightAdjoint : D ⥤ C :=
  Adjunction.rightAdjointOfEquiv (fun X Y ↦ (P Y).homEquiv X)
    (fun _ _ Y f g ↦ (P Y).homEquiv_naturality f g)

/-- The representing bijections give the adjunction and its actual chosen counit.
Source: blueprint proposition-sp-tower-geometric, Charts and gluing.
Proof: the inverse representing bijection sends a map `a` to `F(a)` followed by
its specified counit. Functoriality follows from naturality in the test object.
Mathlib's right-adjoint constructor supplies both triangle identities. Its counit
is the inverse bijection applied to the identity, hence the specified counit.
(blueprint: lem-sp-representing-counits-adjunction) -/
theorem representingCounits_adjunction :
    ∃ adj : F ⊣ representingCounitRightAdjoint P,
      ∀ Y : D, adj.counit.app Y = (P Y).counit := by
  let adj := Adjunction.adjunctionOfEquivRight (fun X Y ↦ (P Y).homEquiv X)
    (fun _ _ Y f g ↦ (P Y).homEquiv_naturality f g)
  refine ⟨adj, ?_⟩
  intro Y
  change F.map (𝟙 (P Y).object) ≫ (P Y).counit = (P Y).counit
  simp

end CategoryTheory
