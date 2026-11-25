/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic

/-! # Coinduction for strict semilinear systems

Source: Stacks 0941, the coinduced sequence construction.
(blueprint: lem-coef-system-coinduced-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace SheafOfModules.SequenceCoinduced
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r}) (n : ℕ)

/-- The coinduced module at a vertex, zero below the input vertex.
Source: Stacks 0941 and 015F (blueprint: lem-coef-system-coinduced-adjunction). -/
def rightLevel (M : systemLevel B n) (k : ℕ) : systemLevel B k :=
  if h : n ≤ k then (systemRestriction B h).obj M else 0

/-- The identification of a nonzero coinduced vertex with scalar restriction.
Source: Stacks 0941 and 015F (blueprint: lem-coef-system-coinduced-adjunction). -/
def rightAboveIso (M : systemLevel B n) {k : ℕ} (hk : n ≤ k) :
    rightLevel B n M k ≅ (systemRestriction B hk).obj M :=
  eqToIso (dite_eq_left hk)

/-- The coinduced transition, given by scalar-restriction coherence above the vertex.
Source: Stacks 0941 and 015F (blueprint: lem-coef-system-coinduced-adjunction). -/
def rightTransition (M : systemLevel B n) {j k : ℕ} (h : j ≤ k) :
    rightLevel B n M k ⟶ (systemRestriction B h).obj (rightLevel B n M j) :=
  if hj : n ≤ j then
    let hk := hj.trans h
    let hc : B.map (homOfLE hk).op =
        B.map (homOfLE h).op ≫ B.map (homOfLE hj).op := by
      rw [← B.map_comp]
      rfl
    (rightAboveIso B n M hk).hom ≫
      (systemScalarRestrictionComposition _ _ _ hc).inv.app M ≫
        (systemRestriction B h).map (rightAboveIso B n M hj).inv
  else 0

/-- Above the input vertex, the transition is the scalar-restriction compositor.
Source: Stacks 0941 (blueprint: lem-coef-system-coinduced-adjunction). -/
theorem rightTransition_above (M : systemLevel B n) {j k : ℕ}
    (h : j ≤ k) (hj : n ≤ j) :
    rightTransition B n M h =
      (rightAboveIso B n M (hj.trans h)).hom ≫
        (systemScalarRestrictionComposition (B.map (homOfLE h).op)
          (B.map (homOfLE hj).op) (B.map (homOfLE (hj.trans h)).op)
          (by rw [← B.map_comp]; rfl)).inv.app M ≫
        (systemRestriction B h).map (rightAboveIso B n M hj).inv := dite_eq_left hj

/-- The coinduced strict system, with its sectionwise identity and composition laws.
Source: Stacks 0941 and 015F (blueprint: lem-coef-system-coinduced-adjunction). -/
def rightObj (M : systemLevel B n) : StrictRingSystem B where
  level := rightLevel B n M
  transition h := rightTransition B n M h
  identity k U x := by
    let η := systemScalarRestrictionUnit (B.map (homOfLE (Nat.le_refl k)).op)
      (B.map_id (op k))
    have he : rightTransition B n M (Nat.le_refl k) =
        η.inv.app (rightLevel B n M k) := by
      by_cases hk : n ≤ k
      · rw [rightTransition_above B n M _ hk]
        apply (cancel_epi (rightAboveIso B n M hk).inv).1
        apply (cancel_mono ((systemRestriction B (Nat.le_refl k)).map
          (rightAboveIso B n M hk).hom)).1
        simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
          Iso.inv_hom_id, CategoryTheory.Functor.map_id]
        rw [← η.inv.naturality]
        simp only [Functor.id_map, Iso.inv_hom_id_assoc]
        ext V y
        rfl
      · have hz : IsZero (rightLevel B n M k) := by
          dsimp only [rightLevel]
          rw [dite_eq_right hk]
          exact isZero_zero _
        exact hz.eq_of_src _ _
    exact congrArg (fun f ↦ f.val.app U x) he
  compose {j k m} h q U x := by
    have hc : B.map (homOfLE (h.trans q)).op =
        B.map (homOfLE q).op ≫ B.map (homOfLE h).op := by
      rw [← B.map_comp]
      rfl
    let η := systemScalarRestrictionComposition _ _ _ hc
    have he : rightTransition B n M (h.trans q) =
        rightTransition B n M q ≫
          (systemRestriction B q).map (rightTransition B n M h) ≫
          η.hom.app (rightLevel B n M j) := by
      by_cases hj : n ≤ j
      · have hk := hj.trans h
        have hm := hk.trans q
        rw [rightTransition_above B n M _ hj, rightTransition_above B n M _ hk,
          rightTransition_above B n M _ hj]
        apply (cancel_epi (rightAboveIso B n M hm).inv).1
        apply (cancel_mono ((systemRestriction B (h.trans q)).map
          (rightAboveIso B n M hj).hom)).1
        simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
        rw [← η.hom.naturality (rightAboveIso B n M hj).hom]
        simp only [Functor.comp_map, ← Functor.map_comp_assoc, ← Functor.map_comp,
          Iso.inv_hom_id, CategoryTheory.Functor.map_id, Iso.inv_hom_id_assoc]
        ext V y
        rfl
      · have hz : IsZero (rightLevel B n M j) := by
          dsimp only [rightLevel]
          rw [dite_eq_right hj]
          exact isZero_zero _
        exact ((systemRestriction B (h.trans q)).map_isZero hz).eq_of_tgt _ _
    exact congrArg (fun f ↦ f.val.app U x) he

/-- The vertexwise action of coinduction on a module morphism.
Source: Stacks 0941 and 015F (blueprint: lem-coef-system-coinduced-adjunction). -/
def rightLevelMap {M N : systemLevel B n} (f : M ⟶ N) (k : ℕ) :
    rightLevel B n M k ⟶ rightLevel B n N k :=
  if hk : n ≤ k then (rightAboveIso B n M hk).hom ≫
    (systemRestriction B hk).map f ≫ (rightAboveIso B n N hk).inv else 0

/-- Above the input vertex, coinduction acts by scalar restriction.
Source: Stacks 0941 and 015F (blueprint: lem-coef-system-coinduced-adjunction). -/
theorem rightLevelMap_above {M N : systemLevel B n} (f : M ⟶ N)
    {k : ℕ} (hk : n ≤ k) :
    rightLevelMap B n f k = (rightAboveIso B n M hk).hom ≫
      (systemRestriction B hk).map f ≫ (rightAboveIso B n N hk).inv := dite_eq_left hk

/-- The strict-system morphism induced by a module morphism.
Source: Stacks 0941 and 015F (blueprint: lem-coef-system-coinduced-adjunction). -/
def rightMap {M N : systemLevel B n} (f : M ⟶ N) :
    rightObj B n M ⟶ rightObj B n N where
  app := rightLevelMap B n f
  comm {j k} h := by
    change rightLevelMap B n f k ≫ rightTransition B n N h =
      rightTransition B n M h ≫ (systemRestriction B h).map (rightLevelMap B n f j)
    by_cases hj : n ≤ j
    · have hk := hj.trans h
      rw [rightLevelMap_above B n f hk, rightTransition_above B n N h hj,
        rightTransition_above B n M h hj, rightLevelMap_above B n f hj]
      apply (cancel_epi (rightAboveIso B n M hk).inv).1
      apply (cancel_mono ((systemRestriction B h).map
        (rightAboveIso B n N hj).hom)).1
      simp only [Category.assoc, Iso.inv_hom_id_assoc,
        ← Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.comp_id]
      exact (systemScalarRestrictionComposition (B.map (homOfLE h).op)
        (B.map (homOfLE hj).op) (B.map (homOfLE hk).op)
        (by rw [← B.map_comp]; rfl)).inv.naturality f
    · have hz : IsZero (rightLevel B n N j) := by
        dsimp only [rightLevel]
        rw [dite_eq_right hj]
        exact isZero_zero _
      exact ((systemRestriction B h).map_isZero hz).eq_of_tgt _ _

/-- The explicit coinduction functor at a fixed vertex.
Source: Stacks 0941 and 015F (blueprint: lem-coef-system-coinduced-adjunction). -/
def rightExtension : systemLevel B n ⥤ StrictRingSystem B where
  obj := rightObj B n
  map := rightMap B n
  map_id M := by
    apply strictRingSystem_hom_ext B
    intro k
    change rightLevelMap B n (𝟙 M) k = 𝟙 _
    by_cases hk : n ≤ k
    · rw [rightLevelMap_above B n _ hk, CategoryTheory.Functor.map_id, Category.id_comp,
        Iso.hom_inv_id]
    · have hz : IsZero (rightLevel B n M k) := by
        dsimp only [rightLevel]
        rw [dite_eq_right hk]
        exact isZero_zero _
      exact hz.eq_of_src _ _
  map_comp {M N P} f g := by
    apply strictRingSystem_hom_ext B
    intro k
    change rightLevelMap B n (f ≫ g) k =
      rightLevelMap B n f k ≫ rightLevelMap B n g k
    by_cases hk : n ≤ k
    · rw [rightLevelMap_above B n _ hk, rightLevelMap_above B n _ hk,
        rightLevelMap_above B n _ hk, Functor.map_comp]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · have hz : IsZero (rightLevel B n M k) := by
        dsimp only [rightLevel]
        rw [dite_eq_right hk]
        exact isZero_zero _
      exact hz.eq_of_src _ _

/-- Coinduction preserves addition, since scalar restriction and zero do so.
Source: Stacks 0941 and 015F (blueprint: lem-coef-system-coinduced-adjunction). -/
instance rightExtension_additive : (rightExtension B n).Additive where
  map_add {M N} f g := by
    apply strictRingSystem_hom_ext B
    intro k
    change (systemEvaluation B k).map ((rightExtension B n).map (f + g)) =
      (systemEvaluation B k).map ((rightExtension B n).map f + (rightExtension B n).map g)
    rw [(systemEvaluation B k).map_add]
    change rightLevelMap B n (f + g) k =
      rightLevelMap B n f k + rightLevelMap B n g k
    by_cases hk : n ≤ k
    · rw [rightLevelMap_above B n _ hk, rightLevelMap_above B n _ hk,
        rightLevelMap_above B n _ hk, Functor.map_add]
      simp only [Preadditive.comp_add, Preadditive.add_comp]
    · have hz : IsZero (rightLevel B n M k) := by
        dsimp only [rightLevel]
        rw [dite_eq_right hk]
        exact isZero_zero _
      exact hz.eq_of_src _ _

/-- Evaluation of coinduction above the input vertex is scalar restriction.
Source: Stacks 0941 and 015F (blueprint: lem-coef-system-coinduced-adjunction). -/
def rightExtension_above {k : ℕ} (hk : n ≤ k) :
    rightExtension B n ⋙ systemEvaluation B k ≅ systemRestriction B hk :=
  NatIso.ofComponents (fun M ↦ rightAboveIso B n M hk) (fun f ↦ by
    change rightLevelMap B n f k ≫ (rightAboveIso B n _ hk).hom = _
    rw [rightLevelMap_above B n f hk]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl)

/-- Extend a map from a vertex using the actual iterated system transitions.
Source: Stacks 0941 and 015F (blueprint: lem-coef-system-coinduced-adjunction). -/
def coextendApp (M : StrictRingSystem B) (N : systemLevel B n)
    (f : M.level n ⟶ N) (k : ℕ) : M.level k ⟶ rightLevel B n N k :=
  if hk : n ≤ k then M.transition hk ≫ (systemRestriction B hk).map f ≫
    (rightAboveIso B n N hk).inv else 0

/-- The coextension formula at a vertex at or above the input vertex.
Source: Stacks 0941 and 015F (blueprint: lem-coef-system-coinduced-adjunction). -/
theorem coextendApp_above (M : StrictRingSystem B) (N : systemLevel B n)
    (f : M.level n ⟶ N) {k : ℕ} (hk : n ≤ k) :
    coextendApp B n M N f k = M.transition hk ≫ (systemRestriction B hk).map f ≫
      (rightAboveIso B n N hk).inv := dite_eq_left hk

/-- Extend a vertex map to its coinduced strict-system morphism.
Source: Stacks 0941 and 015F (blueprint: lem-coef-system-coinduced-adjunction). -/
def coextend (M : StrictRingSystem B) (N : systemLevel B n)
    (f : M.level n ⟶ N) : M ⟶ (rightExtension B n).obj N where
  app := coextendApp B n M N f
  comm {j k} h := by
    change coextendApp B n M N f k ≫ rightTransition B n N h =
      M.transition h ≫ (systemRestriction B h).map (coextendApp B n M N f j)
    by_cases hj : n ≤ j
    · have hk := hj.trans h
      rw [coextendApp_above B n M N f hk, coextendApp_above B n M N f hj,
        rightTransition_above B n N h hj]
      apply (cancel_mono ((systemRestriction B h).map (rightAboveIso B n N hj).hom)).1
      simp only [Category.assoc, Iso.inv_hom_id_assoc,
        ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]
      ext U x
      exact congrArg (fun y ↦ f.val.app U y) (M.compose hj h U x)
    · have hz : IsZero (rightLevel B n N j) := by
        dsimp only [rightLevel]
        rw [dite_eq_right hj]
        exact isZero_zero _
      exact ((systemRestriction B h).map_isZero hz).eq_of_tgt _ _

/-- Recover a vertex map from a coinduced morphism by the scalar unit.
Source: Stacks 0941 and 015F (blueprint: lem-coef-system-coinduced-adjunction). -/
def coevaluate (M : StrictRingSystem B) (N : systemLevel B n)
    (f : M ⟶ (rightExtension B n).obj N) : M.level n ⟶ N :=
  f.app n ≫ (rightAboveIso B n N (Nat.le_refl n)).hom ≫
    (systemScalarRestrictionUnit (B.map (homOfLE (Nat.le_refl n)).op)
      (B.map_id (op n))).hom.app N

attribute [local implicit_reducible] rightExtension rightObj systemEvaluation

/-- Coextension followed by evaluation is the original vertex map.
Source: Stacks 0941 and 015F (blueprint: lem-coef-system-coinduced-adjunction). -/
theorem coevaluate_coextend (M : StrictRingSystem B) (N : systemLevel B n)
    (f : M.level n ⟶ N) : coevaluate B n M N (coextend B n M N f) = f := by
  change (coextendApp B n M N f n) ≫ _ = f
  rw [coextendApp_above B n M N f (Nat.le_refl n)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  ext U x
  exact congrArg (fun y ↦ f.val.app U y) (M.identity n U x)

/-- Evaluation followed by coextension is the original coinduced morphism.
Source: Stacks 0941 and 015F (blueprint: lem-coef-system-coinduced-adjunction). -/
theorem coextend_coevaluate (M : StrictRingSystem B) (N : systemLevel B n)
    (f : M ⟶ (rightExtension B n).obj N) : coextend B n M N (coevaluate B n M N f) = f := by
  apply strictRingSystem_hom_ext B
  intro k
  change coextendApp B n M N (coevaluate B n M N f) k = f.app k
  by_cases hk : n ≤ k
  · rw [coextendApp_above B n M N _ hk]
    apply (cancel_mono (rightAboveIso B n N hk).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have he := f.comm hk
    change f.app k ≫ rightTransition B n N hk =
      M.transition hk ≫ (systemRestriction B hk).map (f.app n) at he
    rw [rightTransition_above B n N hk (Nat.le_refl n)] at he
    dsimp only [coevaluate]
    simp only [Functor.map_comp]
    apply (cancel_mono ((systemScalarRestrictionComposition
      (B.map (homOfLE hk).op) (B.map (homOfLE (Nat.le_refl n)).op)
      (B.map (homOfLE ((Nat.le_refl n).trans hk)).op)
      (by rw [← B.map_comp]; rfl)).inv.app N ≫
      (systemRestriction B hk).map (rightAboveIso B n N (Nat.le_refl n)).inv)).1
    simp only [Category.assoc]
    have hu : (systemRestriction B hk).map
        ((systemScalarRestrictionUnit (B.map (homOfLE (Nat.le_refl n)).op)
          (B.map_id (op n))).hom.app N) ≫
        (systemScalarRestrictionComposition (B.map (homOfLE hk).op)
          (B.map (homOfLE (Nat.le_refl n)).op)
          (B.map (homOfLE ((Nat.le_refl n).trans hk)).op)
          (by rw [← B.map_comp]; rfl)).inv.app N = 𝟙 _ := by
      ext U x
      rfl
    rw [← Category.assoc ((systemRestriction B hk).map
      ((systemScalarRestrictionUnit (B.map (homOfLE (Nat.le_refl n)).op)
        (B.map_id (op n))).hom.app N)), hu, Category.id_comp]
    simp only [← Functor.map_comp, Iso.hom_inv_id, Category.comp_id]
    exact he.symm
  · have hz : IsZero (rightLevel B n N k) := by
      dsimp only [rightLevel]
      rw [dite_eq_right hk]
      exact isZero_zero _
    exact hz.eq_of_tgt _ _

/-- Evaluation at a level has the explicitly constructed coinduced right adjoint.
Source: Stacks 0941 (blueprint: lem-coef-system-coinduced-adjunction).
Proof: extend f:M_n→N at k≥n by the transition M_k→Res(M_n), followed by Res(f),
and put zero below n. The system composition law proves compatibility. Restriction
at n is inverse to this extension: one inverse law is the identity transition,
and the other is the naturality square for n≤k. These formulas commute with maps
in both variables, so the Hom equivalences define the adjunction. -/
def adjunction : systemEvaluation B n ⊣ rightExtension B n := by
  refine Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦
        { toFun := coextend B n M N
          invFun := coevaluate B n M N
          left_inv := coevaluate_coextend B n M N
          right_inv := coextend_coevaluate B n M N }
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro M M' N f g
    ext U x
    rfl
  · intro M N N' f g
    apply strictRingSystem_hom_ext B
    intro k
    change coextendApp B n M N' (f ≫ g) k =
      coextendApp B n M N f k ≫ rightLevelMap B n g k
    by_cases hk : n ≤ k
    · rw [coextendApp_above B n M N' _ hk, coextendApp_above B n M N _ hk,
        rightLevelMap_above B n g hk, Functor.map_comp]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · have hz : IsZero (rightLevel B n N' k) := by
        dsimp only [rightLevel]
        rw [dite_eq_right hk]
        exact isZero_zero _
      exact hz.eq_of_tgt _ _

end SheafOfModules.SequenceCoinduced
