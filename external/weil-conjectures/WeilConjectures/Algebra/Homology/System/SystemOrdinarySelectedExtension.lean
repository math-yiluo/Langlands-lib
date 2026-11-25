/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import WeilConjectures.Algebra.Homology.System.SystemOrdinarySingleExtension

/-! # Ordinary extension from a selected subsequence

Source: Zheng, Construction 4.1; Stacks 03D7 and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (r : ℕ ↪o ℕ)

/-- First-selected indices are monotone for every inequality.
Source: Zheng 4.1, subsequence extension
(blueprint: lem-pur-system-ordinary-selected-extension).
Proof: the first selected level above m is also above l when l is at most m. -/
theorem systemNextSelected_monotone {l m : ℕ} (h : l ≤ m) :
    systemNextSelected r l ≤ systemNextSelected r m :=
  (systemNextSelected_spec r l).2 _ (h.trans (systemNextSelected_spec r m).1)

/-- A selected level selects its own index.
Source: Zheng 4.1, subsequence extension
(blueprint: lem-pur-system-ordinary-selected-extension).
Proof: minimality gives t(r i) at most i, and order reflection gives the reverse
inequality from r i at most r(t(r i)). -/
theorem systemNextSelected_at (i : ℕ) : systemNextSelected r (r i) = i := by
  apply Nat.le_antisymm
  · exact (systemNextSelected_spec r (r i)).2 i le_rfl
  · exact r.le_iff_le.mp (systemNextSelected_spec r (r i)).1

/-- The inverse tensor associator inserts the unit of the middle coefficient ring.
Source: Stacks 03EK (blueprint: lem-pur-system-ordinary-selected-extension).
Proof: apply the injective forward associator. Its normalized formula multiplies
by the image of one, giving the original tensor; the isomorphism inverse law finishes. -/
theorem systemTensorAssoc_inv_tmul {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
    (P : systemLevel B n) (U : Cᵒᵖ) (c : (B.obj (op l)).obj.obj U)
    (x : P.val.obj U) :
    ((T.ordinaryAssoc B h k).inv.app P).val.app U
      (systemModelTmul (S (B.map (homOfLE (h.trans k)).op)).model P U c x) =
    systemModelTmul (S (B.map (homOfLE h).op)).model ((systemTensor S B k).obj P) U c
      (systemModelTmul (S (B.map (homOfLE k).op)).model P U 1 x) := by
  have hinj : Function.Injective (((T.ordinaryAssoc B h k).hom.app P).val.app U) := by
    apply Function.LeftInverse.injective
      (g := fun z ↦ ((T.ordinaryAssoc B h k).inv.app P).val.app U z)
    intro z
    exact congrArg (fun t ↦ t.val.app U z) ((T.ordinaryAssoc B h k).hom_inv_id_app P)
  apply hinj
  have hi := congrArg (fun t ↦ t.val.app U
    (systemModelTmul (S (B.map (homOfLE (h.trans k)).op)).model P U c x))
    ((T.ordinaryAssoc B h k).inv_hom_id_app P)
  change ((T.ordinaryAssoc B h k).hom.app P).val.app U
    (((T.ordinaryAssoc B h k).inv.app P).val.app U _) = _ at hi
  rw [hi, T.assoc_normalized, map_one, mul_one]
  rfl

/-- The tensor module at one level of selected extension.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension). -/
abbrev systemSelectedLevel (P : StrictRingSystem (selectedSystemRings B r)) (m : ℕ) :=
  (systemTensor S B (systemNextSelected_spec r m).1).obj
    (P.level (systemNextSelected r m))

/-- Selected extension transitions are the adjuncts of the scalar-extended strict
transitions, with their actual tensor associators.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension). -/
def systemSelectedTransition (P : StrictRingSystem (selectedSystemRings B r))
    {l m : ℕ} (h : l ≤ m) : systemSelectedLevel S B r P m ⟶
      (systemRestriction B h).obj (systemSelectedLevel S B r P l) :=
  (systemTensorAdj S B h).homEquiv _ _
    ((T.ordinaryAssoc B h (systemNextSelected_spec r m).1).hom.app _ ≫
      (T.ordinaryAssoc B (systemNextSelected_spec r l).1
        (r.monotone (systemNextSelected_monotone r h))).inv.app _ ≫
      (systemTensor S B (systemNextSelected_spec r l).1).map
        (((systemTensorAdj S (selectedSystemRings B r)
          (systemNextSelected_monotone r h)).homEquiv _ _).symm
            (P.transition (systemNextSelected_monotone r h))))

/-- The selected transition sends c tensor x to the image of c tensor the actual
selected transition of x. Source: Zheng 4.1; Stacks 03EK
(blueprint: lem-pur-system-ordinary-selected-extension).
Proof: transpose using the unit tensor, apply the forward associator, insert one
by the inverse associator, and apply the scalar adjunct to the strict transition.
The resulting middle scalar is one and acts trivially. -/
theorem systemSelectedTransition_tmul (P : StrictRingSystem (selectedSystemRings B r))
    {l m : ℕ} (h : l ≤ m) (U : Cᵒᵖ) (c : (B.obj (op m)).obj.obj U)
    (x : (P.level (systemNextSelected r m)).val.obj U) :
    (systemSelectedTransition S T B r P h).val.app U
      (systemModelTmul (S (B.map (homOfLE (systemNextSelected_spec r m).1).op)).model
        (P.level (systemNextSelected r m)) U c x) =
    systemModelTmul (S (B.map (homOfLE (systemNextSelected_spec r l).1).op)).model
      (P.level (systemNextSelected r l)) U
      ((B.map (homOfLE h).op).hom.app U c)
      ((P.transition (systemNextSelected_monotone r h)).val.app U x) := by
  dsimp only [systemSelectedTransition]
  rw [Adjunction.homEquiv_unit]
  change ((T.ordinaryAssoc B h (systemNextSelected_spec r m).1).hom.app _ ≫
      (T.ordinaryAssoc B (systemNextSelected_spec r l).1
        (r.monotone (systemNextSelected_monotone r h))).inv.app _ ≫
      (systemTensor S B (systemNextSelected_spec r l).1).map _).val.app U
    (((S (B.map (homOfLE h).op)).ordinaryAdj.unit.app _).val.app U _) = _
  rw [(S (B.map (homOfLE h).op)).unit_normalized]
  change ((systemTensor S B (systemNextSelected_spec r l).1).map _).val.app U
    (((T.ordinaryAssoc B (systemNextSelected_spec r l).1
      (r.monotone (systemNextSelected_monotone r h))).inv.app _).val.app U
      (((T.ordinaryAssoc B h (systemNextSelected_spec r m).1).hom.app _).val.app U _)) = _
  rw [T.assoc_normalized, one_mul, systemTensorAssoc_inv_tmul, systemScalarModel_map_tmul]
  congr 1
  have ht := systemScalarModel_transpose_tmul
    (S ((selectedSystemRings B r).map (homOfLE (systemNextSelected_monotone r h)).op))
    (P.level (systemNextSelected r m)) (P.level (systemNextSelected r l))
    (((systemTensorAdj S (selectedSystemRings B r)
      (systemNextSelected_monotone r h)).homEquiv _ _).symm
        (P.transition (systemNextSelected_monotone r h))) U 1 x
  rw [Equiv.apply_symm_apply, one_smul] at ht
  exact ht

/-- The identity transition of selected extension is the identity on sections.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension).
Proof: compare with the identity-on-sections coefficient restriction unit. On unit
tensors the transition formula reduces to the identity transition of P. -/
theorem systemSelectedTransition_identity (P : StrictRingSystem (selectedSystemRings B r))
    (m : ℕ) (U : Cᵒᵖ) (x : (systemSelectedLevel S B r P m).val.obj U) :
    (systemSelectedTransition S T B r P (Nat.le_refl m)).val.app U x = x := by
  let η := systemScalarRestrictionUnit (B.map (homOfLE (Nat.le_refl m)).op)
    (B.map_id (op m))
  have he : systemSelectedTransition S T B r P (Nat.le_refl m) =
      η.inv.app (systemSelectedLevel S B r P m) := by
    apply systemScalarModel_hom_ext (S (B.map (homOfLE (systemNextSelected_spec r m).1).op))
    intro V y
    change (systemSelectedTransition S T B r P (Nat.le_refl m)).val.app V _ = _
    rw [systemSelectedTransition_tmul, map_one, P.identity]
    rfl
  exact congrArg (fun f ↦ f.val.app U x) he

/-- Selected extension transitions compose, including repeated selected indices.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension).
Proof: compare the direct transition with the composite through the canonical
identity-on-sections restriction compositor. On unit tensors both are the tensor of
the corresponding composite transition of P; P's strict composition law identifies them. -/
theorem systemSelectedTransition_compose (P : StrictRingSystem (selectedSystemRings B r))
    {l m k : ℕ} (h : l ≤ m) (q : m ≤ k) (U : Cᵒᵖ)
    (x : (systemSelectedLevel S B r P k).val.obj U) :
    (systemSelectedTransition S T B r P (h.trans q)).val.app U x =
      (systemSelectedTransition S T B r P h).val.app U
        ((systemSelectedTransition S T B r P q).val.app U x) := by
  have hc : B.map (homOfLE (h.trans q)).op =
      B.map (homOfLE q).op ≫ B.map (homOfLE h).op := by
    rw [← B.map_comp]
    rfl
  let η := systemScalarRestrictionComposition _ _ _ hc
  have he : systemSelectedTransition S T B r P (h.trans q) =
      systemSelectedTransition S T B r P q ≫
        (systemRestriction B q).map (systemSelectedTransition S T B r P h) ≫
        η.hom.app (systemSelectedLevel S B r P l) := by
    apply systemScalarModel_hom_ext (S (B.map (homOfLE (systemNextSelected_spec r k).1).op))
    intro V y
    change (systemSelectedTransition S T B r P (h.trans q)).val.app V _ =
      (systemSelectedTransition S T B r P h).val.app V
        ((systemSelectedTransition S T B r P q).val.app V _)
    rw [systemSelectedTransition_tmul, systemSelectedTransition_tmul]
    simp only [map_one]
    rw [systemSelectedTransition_tmul]
    simp only [map_one]
    rw [P.compose]
  exact congrArg (fun f ↦ f.val.app U x) he

/-- The strict system underlying selected extension.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension). -/
def systemSelectedObject (P : StrictRingSystem (selectedSystemRings B r)) :
    StrictRingSystem B where
  level := systemSelectedLevel S B r P
  transition := systemSelectedTransition S T B r P
  identity := systemSelectedTransition_identity S T B r P
  compose := systemSelectedTransition_compose S T B r P

/-- The component of selected extension on a strict morphism.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension). -/
def systemSelectedMapLevel {P Q : StrictRingSystem (selectedSystemRings B r)}
    (f : P ⟶ Q) (m : ℕ) : systemSelectedLevel S B r P m ⟶ systemSelectedLevel S B r Q m :=
  (systemTensor S B (systemNextSelected_spec r m).1).map (f.app (systemNextSelected r m))

/-- Extended maps commute with the tensor transitions.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension).
Proof: test on unit tensors and use the original strict morphism's transition square. -/
theorem systemSelectedMap_comm {P Q : StrictRingSystem (selectedSystemRings B r)}
    (f : P ⟶ Q) {l m : ℕ} (h : l ≤ m) :
    systemSelectedMapLevel S B r f m ≫ systemSelectedTransition S T B r Q h =
      systemSelectedTransition S T B r P h ≫
        (systemRestriction B h).map (systemSelectedMapLevel S B r f l) := by
  apply systemScalarModel_hom_ext (S (B.map (homOfLE (systemNextSelected_spec r m).1).op))
  intro U x
  change (systemSelectedTransition S T B r Q h).val.app U
    (((systemTensor S B (systemNextSelected_spec r m).1).map
      (f.app (systemNextSelected r m))).val.app U _) =
    ((systemTensor S B (systemNextSelected_spec r l).1).map
      (f.app (systemNextSelected r l))).val.app U
        ((systemSelectedTransition S T B r P h).val.app U _)
  rw [systemScalarModel_map_tmul, systemSelectedTransition_tmul,
    systemSelectedTransition_tmul, systemScalarModel_map_tmul]
  have he := congrArg (fun t ↦ t.val.app U x)
    (f.comm (systemNextSelected_monotone r h))
  exact congrArg (fun y ↦ systemModelTmul
    (S (B.map (homOfLE (systemNextSelected_spec r l).1).op)).model
      (Q.level (systemNextSelected r l)) U
        ((B.map (homOfLE h).op).hom.app U 1) y) he

/-- Ordinary left extension from the selected-index system.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension). -/
def systemSelectedFunctor : StrictRingSystem (selectedSystemRings B r) ⥤ StrictRingSystem B where
  obj := systemSelectedObject S T B r
  map f := { app := systemSelectedMapLevel S B r f
             comm := systemSelectedMap_comm S T B r f }
  map_id P := by
    apply strictRingSystem_hom_ext B
    intro m
    exact (systemTensor S B (systemNextSelected_spec r m).1).map_id _
  map_comp f g := by
    apply strictRingSystem_hom_ext B
    intro m
    exact (systemTensor S B (systemNextSelected_spec r m).1).map_comp _ _

/-- Evaluating ordinary selected extension gives its prescribed single tensor term.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension). -/
def systemSelectedBelow (m : ℕ) :
    systemSelectedFunctor S T B r ⋙ systemEvaluation B m ≅
      systemEvaluation (selectedSystemRings B r) (systemNextSelected r m) ⋙
        systemTensor S B (systemNextSelected_spec r m).1 := Iso.refl _

/-- Transport between sections at equal selected indices.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension). -/
def systemSelectedIndexCast (P : StrictRingSystem (selectedSystemRings B r))
    {a i : ℕ} (ha : a = i) (U : Cᵒᵖ) (x : (P.level a).val.obj U) :
    (P.level i).val.obj U :=
  Eq.mp (congrArg (fun j ↦ ((P.level j).val.obj U : Type w)) ha) x

/-- At equal selected indices the tensor is the scalar unit, with explicit transport.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension). -/
def systemSelectedEqualIndex (P : StrictRingSystem (selectedSystemRings B r))
    {a i : ℕ} (ha : a = i) (h : r i ≤ r a) :
    (systemTensor S B h).obj (P.level a) ≅ P.level i := by
  subst a
  exact (T.ordinaryUnit B (r i)).app (P.level i)

/-- The inverse equal-index tensor unit inserts one tensor and transports the index.
Source: Stacks 03EK (blueprint: lem-pur-system-ordinary-selected-extension).
Proof: substitute the index equality. The transported section is then unchanged,
and the assertion is the inverse scalar unit's tensor formula. -/
theorem systemSelectedEqualIndex_inv_tmul
    (P : StrictRingSystem (selectedSystemRings B r)) {a i : ℕ}
    (ha : a = i) (h : r i ≤ r a) (U : Cᵒᵖ) (x : (P.level i).val.obj U) :
    ((systemSelectedEqualIndex S T B r P ha h).inv).val.app U x =
      systemModelTmul (S (B.map (homOfLE h).op)).model (P.level a) U 1
        (systemSelectedIndexCast B r P ha.symm U x) := by
  subst a
  dsimp only [systemSelectedEqualIndex, systemSelectedIndexCast]
  exact systemTensorUnit_inv_tmul S T B (r i) (P.level i) U x

/-- The tensor identification at a selected level is the scalar unit.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension). -/
def systemSelectedAtSelected (P : StrictRingSystem (selectedSystemRings B r)) (i : ℕ) :
    systemSelectedLevel S B r P (r i) ≅ P.level i :=
  systemSelectedEqualIndex S T B r P (systemNextSelected_at r i)
    (systemNextSelected_spec r (r i)).1

/-- In selected-level coordinates the inverse scalar unit inserts one tensor.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension).
Proof: apply the equal-index inverse unit formula to t(r i) equals i. -/
theorem systemSelectedAtSelected_inv_tmul
    (P : StrictRingSystem (selectedSystemRings B r)) (i : ℕ) (U : Cᵒᵖ)
    (x : (P.level i).val.obj U) :
    ((systemSelectedAtSelected S T B r P i).inv).val.app U x =
      systemModelTmul (S (B.map (homOfLE (systemNextSelected_spec r (r i)).1).op)).model
        (P.level (systemNextSelected r (r i))) U 1
          (systemSelectedIndexCast B r P (systemNextSelected_at r i).symm U x) :=
  systemSelectedEqualIndex_inv_tmul S T B r P (systemNextSelected_at r i) _ U x

/-- Index transport commutes with strict transitions.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension).
Proof: substitute both index equalities; the inequality proofs then agree. -/
theorem systemSelectedIndexCast_transition (P : StrictRingSystem (selectedSystemRings B r))
    {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (h : b ≤ a) (h' : b' ≤ a')
    (U : Cᵒᵖ) (x : (P.level a).val.obj U) :
    systemSelectedIndexCast B r P hb U ((P.transition h).val.app U x) =
      (P.transition h').val.app U (systemSelectedIndexCast B r P ha U x) := by
  subst a'
  subst b'
  rfl

/-- Transport across an equal-index transition cancels its index cast.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension).
Proof: substitute the equality and use the identity transition law. -/
theorem systemSelectedIndexCast_identity (P : StrictRingSystem (selectedSystemRings B r))
    {a i : ℕ} (ha : a = i) (h : i ≤ a) (U : Cᵒᵖ) (x : (P.level i).val.obj U) :
    (P.transition h).val.app U (systemSelectedIndexCast B r P ha.symm U x) = x := by
  subst a
  exact P.identity i U x

/-- At selected indices the inverse tensor units form the strict adjunction unit.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension).
Proof: on each section the unit inserts one. The selected transition maps that
one to one, and its original transition commutes with the equal-index casts. -/
def systemSelectedUnit (P : StrictRingSystem (selectedSystemRings B r)) :
    P ⟶ (systemSubsequence B r).obj ((systemSelectedFunctor S T B r).obj P) where
  app i := (systemSelectedAtSelected S T B r P i).inv
  comm := by
    intro i j h
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    change (systemSelectedTransition S T B r P (r.monotone h)).val.app U
      (((systemSelectedAtSelected S T B r P j).inv).val.app U x) =
      ((systemSelectedAtSelected S T B r P i).inv).val.app U
        ((P.transition h).val.app U x)
    rw [systemSelectedAtSelected_inv_tmul, systemSelectedTransition_tmul, map_one,
      systemSelectedAtSelected_inv_tmul]
    congr 1
    exact (systemSelectedIndexCast_transition B r P (systemNextSelected_at r j).symm
      (systemNextSelected_at r i).symm h _ U x).symm

/-- Scalar transposition extends a map from the selected restriction at every level.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension). -/
def systemSelectedAdjunctLevel (P : StrictRingSystem (selectedSystemRings B r))
    (M : StrictRingSystem B) (f : P ⟶ (systemSubsequence B r).obj M) (m : ℕ) :
    systemSelectedLevel S B r P m ⟶ M.level m :=
  ((systemTensorAdj S B (systemNextSelected_spec r m).1).homEquiv _ _).symm
    (f.app (systemNextSelected r m) ≫ M.transition (systemNextSelected_spec r m).1)

/-- The selected adjunct sends c tensor x to c times the transition of f(x).
Source: Zheng 4.1; Stacks 03D7
(blueprint: lem-pur-system-ordinary-selected-extension).
Proof: apply scalar tensor transposition and the inverse law of its Hom bijection. -/
theorem systemSelectedAdjunctLevel_tmul (P : StrictRingSystem (selectedSystemRings B r))
    (M : StrictRingSystem B) (f : P ⟶ (systemSubsequence B r).obj M) (m : ℕ)
    (U : Cᵒᵖ) (c : (B.obj (op m)).obj.obj U)
    (x : (P.level (systemNextSelected r m)).val.obj U) :
    (systemSelectedAdjunctLevel S B r P M f m).val.app U
      (systemModelTmul (S (B.map (homOfLE (systemNextSelected_spec r m).1).op)).model
        (P.level (systemNextSelected r m)) U c x) =
    c • (show (M.level m).val.obj U from
      (M.transition (systemNextSelected_spec r m).1).val.app U
        ((f.app (systemNextSelected r m)).val.app U x)) := by
  have ht := systemScalarModel_transpose_tmul
    (S (B.map (homOfLE (systemNextSelected_spec r m).1).op))
    (P.level (systemNextSelected r m)) (M.level m)
    (systemSelectedAdjunctLevel S B r P M f m) U c x
  dsimp only [systemSelectedAdjunctLevel] at ht
  rw [Equiv.apply_symm_apply] at ht
  exact ht

/-- The extended maps commute with all strict transitions.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension).
Proof: on a unit tensor, the first path is the composite transition in M applied
to f at the upper selected index. The other path first uses P's transition. The
strict square for f identifies them, and composition of M's transitions finishes. -/
theorem systemSelectedAdjunct_comm (P : StrictRingSystem (selectedSystemRings B r))
    (M : StrictRingSystem B) (f : P ⟶ (systemSubsequence B r).obj M)
    {l m : ℕ} (h : l ≤ m) :
    systemSelectedAdjunctLevel S B r P M f m ≫ M.transition h =
      systemSelectedTransition S T B r P h ≫
        (systemRestriction B h).map (systemSelectedAdjunctLevel S B r P M f l) := by
  apply systemScalarModel_hom_ext (S (B.map (homOfLE (systemNextSelected_spec r m).1).op))
  intro U x
  change (M.transition h).val.app U
    ((systemSelectedAdjunctLevel S B r P M f m).val.app U _) =
    (systemSelectedAdjunctLevel S B r P M f l).val.app U
      ((systemSelectedTransition S T B r P h).val.app U _)
  rw [systemSelectedAdjunctLevel_tmul, one_smul, systemSelectedTransition_tmul,
    map_one, systemSelectedAdjunctLevel_tmul, one_smul]
  have he := congrArg (fun t ↦ t.val.app U x)
    (f.comm (systemNextSelected_monotone r h))
  change (M.transition (r.monotone (systemNextSelected_monotone r h))).val.app U
    ((f.app (systemNextSelected r m)).val.app U x) =
    (f.app (systemNextSelected r l)).val.app U
      ((P.transition (systemNextSelected_monotone r h)).val.app U x) at he
  rw [← he, ← M.compose, ← M.compose]

/-- The strict map supplied by selected scalar transposition.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension). -/
def systemSelectedAdjunct (P : StrictRingSystem (selectedSystemRings B r))
    (M : StrictRingSystem B) (f : P ⟶ (systemSubsequence B r).obj M) :
    (systemSelectedFunctor S T B r).obj P ⟶ M where
  app := systemSelectedAdjunctLevel S B r P M f
  comm := systemSelectedAdjunct_comm S T B r P M f

/-- A selected restriction map and its equal-index transition cancel the index cast.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension).
Proof: substitute the index equality and use the identity transition in M. -/
theorem systemSelectedAdjunct_selected
    (P : StrictRingSystem (selectedSystemRings B r)) (M : StrictRingSystem B)
    (f : P ⟶ (systemSubsequence B r).obj M) {a i : ℕ} (ha : a = i)
    (h : r i ≤ r a) (U : Cᵒᵖ) (x : (P.level i).val.obj U) :
    (M.transition h).val.app U ((f.app a).val.app U
      (systemSelectedIndexCast B r P ha.symm U x)) = (f.app i).val.app U x := by
  subst a
  rw [M.identity]
  rfl

/-- Restricting the selected adjunct and composing its unit recovers the input map.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension).
Proof: the unit inserts one with its equal-index transport. The adjunct's scalar
formula reduces to the equal-index cancellation lemma. -/
theorem systemSelectedAdjunct_right_inv
    (P : StrictRingSystem (selectedSystemRings B r)) (M : StrictRingSystem B)
    (f : P ⟶ (systemSubsequence B r).obj M) :
    systemSelectedUnit S T B r P ≫ (systemSubsequence B r).map
      (systemSelectedAdjunct S T B r P M f) = f := by
  apply strictRingSystem_hom_ext (selectedSystemRings B r)
  intro i
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change (systemSelectedAdjunctLevel S B r P M f (r i)).val.app U
    (((systemSelectedAtSelected S T B r P i).inv).val.app U x) = _
  rw [systemSelectedAtSelected_inv_tmul, systemSelectedAdjunctLevel_tmul, one_smul]
  exact systemSelectedAdjunct_selected B r P M f (systemNextSelected_at r i) _ U x

/-- The transition from the selected level above m sends the selected unit of x to
one tensor x at m. Source: Zheng 4.1
(blueprint: lem-pur-system-ordinary-selected-extension).
Proof: use the transition's tensor formula. Its scalar is one. Its selected transition
is between the equal indices t(r(t(m))) and t(m), so it cancels the index cast. -/
theorem systemSelectedTransition_unit
    (P : StrictRingSystem (selectedSystemRings B r)) (m : ℕ) (U : Cᵒᵖ)
    (x : (P.level (systemNextSelected r m)).val.obj U) :
    (systemSelectedTransition S T B r P (systemNextSelected_spec r m).1).val.app U
      (((systemSelectedAtSelected S T B r P (systemNextSelected r m)).inv).val.app U x) =
    systemModelTmul (S (B.map (homOfLE (systemNextSelected_spec r m).1).op)).model
      (P.level (systemNextSelected r m)) U 1 x := by
  rw [systemSelectedAtSelected_inv_tmul, systemSelectedTransition_tmul, map_one]
  rw [systemSelectedIndexCast_identity B r P (systemNextSelected_at r _) _ U x]

/-- Adjunction transposition followed by restriction recovers the strict map.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension).
Proof: test at each level on unit tensors. The adjunct uses f at the selected level
above m and then M's transition. The strict square for f moves the transition before
f, where the preceding selected-unit transition formula identifies the tensor. -/
theorem systemSelectedAdjunct_left_inv
    (P : StrictRingSystem (selectedSystemRings B r)) (M : StrictRingSystem B)
    (f : (systemSelectedFunctor S T B r).obj P ⟶ M) :
    systemSelectedAdjunct S T B r P M
      (systemSelectedUnit S T B r P ≫ (systemSubsequence B r).map f) = f := by
  apply strictRingSystem_hom_ext B
  intro m
  apply systemScalarModel_hom_ext (S (B.map (homOfLE (systemNextSelected_spec r m).1).op))
  intro U x
  change (systemSelectedAdjunctLevel S B r P M
      (systemSelectedUnit S T B r P ≫ (systemSubsequence B r).map f) m).val.app U _ = _
  rw [systemSelectedAdjunctLevel_tmul, one_smul]
  have he := congrArg (fun t ↦ t.val.app U
    (((systemSelectedAtSelected S T B r P (systemNextSelected r m)).inv).val.app U x))
    (f.comm (systemNextSelected_spec r m).1)
  change (M.transition (systemNextSelected_spec r m).1).val.app U
    ((f.app (r (systemNextSelected r m))).val.app U _) =
    (f.app m).val.app U
      ((systemSelectedTransition S T B r P (systemNextSelected_spec r m).1).val.app U _) at he
  rw [systemSelectedTransition_unit] at he
  exact he

/-- The selected extension is left adjoint to actual restriction to the subsequence.
Source: Zheng 4.1; Stacks 03D7
(blueprint: lem-pur-system-ordinary-selected-extension).
Proof: the forward map restricts f and precomposes with the selected scalar units.
The inverse is the scalar adjunct construction. The preceding two lemmas show the
inverse laws. Naturality on the left is scalar-extension naturality on unit tensors;
naturality on the right is associativity and restriction functoriality. -/
def systemSelectedAdjunction : systemSelectedFunctor S T B r ⊣ systemSubsequence B r :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P M ↦
        { toFun := fun f ↦ systemSelectedUnit S T B r P ≫ (systemSubsequence B r).map f
          invFun := systemSelectedAdjunct S T B r P M
          left_inv := systemSelectedAdjunct_left_inv S T B r P M
          right_inv := systemSelectedAdjunct_right_inv S T B r P M }
      homEquiv_naturality_left_symm := by
        intro P Q M f g
        apply strictRingSystem_hom_ext B
        intro m
        apply systemScalarModel_hom_ext
          (S (B.map (homOfLE (systemNextSelected_spec r m).1).op))
        intro U x
        change (systemSelectedAdjunctLevel S B r P M (f ≫ g) m).val.app U _ =
          (systemSelectedAdjunctLevel S B r Q M g m).val.app U
            (((systemTensor S B (systemNextSelected_spec r m).1).map
              (f.app (systemNextSelected r m))).val.app U _)
        rw [systemScalarModel_map_tmul, systemSelectedAdjunctLevel_tmul, one_smul,
          systemSelectedAdjunctLevel_tmul, one_smul]
        rfl
      homEquiv_naturality_right := by
        intro P M N f g
        change systemSelectedUnit S T B r P ≫
          ((systemSubsequence B r).map f ≫ (systemSubsequence B r).map g) =
          (systemSelectedUnit S T B r P ≫ (systemSubsequence B r).map f) ≫
            (systemSubsequence B r).map g
        exact (Category.assoc _ _ _).symm }

/-- Ordinary selected extension is additive componentwise.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension). -/
instance systemSelectedFunctorAdditive : (systemSelectedFunctor S T B r).Additive where
  map_add := by
    intro P Q f g
    apply strictRingSystem_hom_ext B
    intro m
    have he := (systemEvaluation B m).map_add
      (f := (systemSelectedFunctor S T B r).map f)
      (g := (systemSelectedFunctor S T B r).map g)
    change systemSelectedMapLevel S B r (f + g) m = _
    apply Eq.trans (b := systemSelectedMapLevel S B r f m + systemSelectedMapLevel S B r g m)
    · change (systemTensor S B (systemNextSelected_spec r m).1).map
        ((systemEvaluation (selectedSystemRings B r) (systemNextSelected r m)).map (f + g)) = _
      rw [Functor.map_add, Functor.map_add]
      rfl
    · exact he.symm

/-- The ordinary selected tensor formula intertwines actual transposes.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-selected-extension).
Proof: evaluate scalar transposition on its unit tensor. Naturality of the strict
map at the arrow from r(t(m)) to m moves the system transition before f. The selected
unit transition formula identifies its value with one tensor x. -/
theorem systemSelectedTranspose (m : ℕ) (P : StrictRingSystem (selectedSystemRings B r))
    (M : StrictRingSystem B) (f : (systemSelectedFunctor S T B r).obj P ⟶ M) :
    (systemTensorAdj S B (systemNextSelected_spec r m).1).homEquiv
      (P.level (systemNextSelected r m)) (M.level m)
      ((systemSelectedBelow S T B r m).inv.app P ≫ (systemEvaluation B m).map f) =
    (systemEvaluation (selectedSystemRings B r) (systemNextSelected r m)).map
      ((systemSelectedAdjunction S T B r).homEquiv P M f) ≫
        M.transition (systemNextSelected_spec r m).1 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  rw [Adjunction.homEquiv_unit]
  change (f.app m).val.app U
    (((S (B.map (homOfLE (systemNextSelected_spec r m).1).op)).ordinaryAdj.unit.app _).val.app
      U x) = _
  rw [(S (B.map (homOfLE (systemNextSelected_spec r m).1).op)).unit_normalized]
  have he := congrArg (fun t ↦ t.val.app U
    (((systemSelectedAtSelected S T B r P (systemNextSelected r m)).inv).val.app U x))
    (f.comm (systemNextSelected_spec r m).1)
  change (M.transition (systemNextSelected_spec r m).1).val.app U
    ((f.app (r (systemNextSelected r m))).val.app U _) =
    (f.app m).val.app U
      ((systemSelectedTransition S T B r P (systemNextSelected_spec r m).1).val.app U _) at he
  rw [systemSelectedTransition_unit] at he
  exact he.symm

end SheafOfModules
