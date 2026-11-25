/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators

/-! # Ordinary extension from one coefficient level

Source: Zheng, Construction 4.1; Stacks 03D7 and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ)

/-- The scalar-adjoint tensor transition below the selected level.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension). -/
def systemSingleBelowTransition (P : systemLevel B n) {l m : ℕ}
    (h : l ≤ m) (hm : m ≤ n) :
    (systemTensor S B hm).obj P ⟶
      (systemRestriction B h).obj ((systemTensor S B (h.trans hm)).obj P) :=
  (systemTensorAdj S B h).homEquiv _ _ ((T.ordinaryAssoc B h hm).hom.app P)

/-- The below-level transition changes the scalar through the actual coefficient map.
Source: Zheng 4.1; Stacks 03EK
(blueprint: lem-pur-system-ordinary-single-extension).
Proof: the transition is the transpose of the associator. Its unit inserts one tensor,
and the normalized associator multiplies that one with the image of the original scalar. -/
theorem systemSingleBelowTransition_tmul (P : systemLevel B n) {l m : ℕ}
    (h : l ≤ m) (hm : m ≤ n) (U : Cᵒᵖ) (c : (B.obj (op m)).obj.obj U)
    (x : P.val.obj U) :
    ((systemSingleBelowTransition S T B n P h hm).val.app U)
      (systemModelTmul (S (B.map (homOfLE hm).op)).model P U c x) =
    systemModelTmul (S (B.map (homOfLE (h.trans hm)).op)).model P U
      ((B.map (homOfLE h).op).hom.app U c) x := by
  dsimp only [systemSingleBelowTransition]
  rw [Adjunction.homEquiv_unit]
  change ((T.ordinaryAssoc B h hm).hom.app P).val.app U
    (((S (B.map (homOfLE h).op)).ordinaryAdj.unit.app
      ((systemTensor S B hm).obj P)).val.app U _) = _
  rw [(S (B.map (homOfLE h).op)).unit_normalized]
  rw [T.assoc_normalized]
  simp only [one_mul]

/-- The actual level of extension from n, with zero above n.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension). -/
def systemSingleLevel (P : systemLevel B n) (m : ℕ) : systemLevel B m :=
  if h : m ≤ n then (systemTensor S B h).obj P else 0

/-- Below n the constructed level is the prescribed tensor extension.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension). -/
def systemSingleLevelBelow (P : systemLevel B n) {m : ℕ} (h : m ≤ n) :
    systemSingleLevel S B n P m ≅ (systemTensor S B h).obj P :=
  eqToIso (dite_eq_left h)

/-- The transition below n is the tensor transition; from a zero level it is zero.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension). -/
def systemSingleTransition (P : systemLevel B n) {l m : ℕ} (h : l ≤ m) :
    systemSingleLevel S B n P m ⟶
      (systemRestriction B h).obj (systemSingleLevel S B n P l) :=
  if hm : m ≤ n then
    (systemSingleLevelBelow S B n P hm).hom ≫
      systemSingleBelowTransition S T B n P h hm ≫
        (systemRestriction B h).map (systemSingleLevelBelow S B n P (h.trans hm)).inv
  else 0

/-- The below-level coordinates remove all branch transports in the transition.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension).
Proof: expand the positive branch and cancel the two level identifications. -/
theorem systemSingleTransition_below (P : systemLevel B n) {l m : ℕ}
    (h : l ≤ m) (hm : m ≤ n) :
    (systemSingleLevelBelow S B n P hm).inv ≫ systemSingleTransition S T B n P h =
      systemSingleBelowTransition S T B n P h hm ≫
        (systemRestriction B h).map (systemSingleLevelBelow S B n P (h.trans hm)).inv := by
  dsimp only [systemSingleTransition]
  rw [dite_eq_left hm]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The constructed transition has the expected formula on each local generator.
Source: Zheng 4.1; Stacks 03EK
(blueprint: lem-pur-system-ordinary-single-extension).
Proof: cancel the below-level coordinate isomorphism and apply the pure tensor formula
for the scalar-adjoint transition. -/
theorem systemSingleTransition_tmul (P : systemLevel B n) {l m : ℕ}
    (h : l ≤ m) (hm : m ≤ n) (U : Cᵒᵖ) (c : (B.obj (op m)).obj.obj U)
    (x : P.val.obj U) :
    (systemSingleTransition S T B n P h).val.app U
      ((systemSingleLevelBelow S B n P hm).inv.val.app U
        (systemModelTmul (S (B.map (homOfLE hm).op)).model P U c x)) =
    (systemSingleLevelBelow S B n P (h.trans hm)).inv.val.app U
      (systemModelTmul (S (B.map (homOfLE (h.trans hm)).op)).model P U
        ((B.map (homOfLE h).op).hom.app U c) x) := by
  have he := congrArg (fun f ↦ f.val.app U
    (systemModelTmul (S (B.map (homOfLE hm).op)).model P U c x))
      (systemSingleTransition_below S T B n P h hm)
  change (systemSingleTransition S T B n P h).val.app U
      ((systemSingleLevelBelow S B n P hm).inv.val.app U _) =
    (systemSingleLevelBelow S B n P (h.trans hm)).inv.val.app U
      ((systemSingleBelowTransition S T B n P h hm).val.app U _) at he
  rw [systemSingleBelowTransition_tmul] at he
  exact he

/-- Above n the chosen ordinary level is a zero object.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension).
Proof: the defining branch is the zero object. -/
theorem systemSingleLevelAbove (P : systemLevel B n) {m : ℕ} (h : n < m) :
    IsZero (systemSingleLevel S B n P m) := by
  dsimp only [systemSingleLevel]
  rw [dite_eq_right (Nat.not_le_of_lt h)]
  exact isZero_zero (systemLevel B m)

/-- Unit tensors detect morphisms out of any constructed level, with the zero case automatic.
Source: Zheng 4.1; Stacks 03EK
(blueprint: lem-pur-system-ordinary-single-extension).
Proof: below n transport along the tensor-level identification and apply scalar Hom
injectivity. Above n every map from the zero object is equal. -/
theorem systemSingleLevel_hom_ext (P : systemLevel B n) (m : ℕ) (M : systemLevel B m)
    (f g : systemSingleLevel S B n P m ⟶ M)
    (h : ∀ (hm : m ≤ n) U x,
      f.val.app U ((systemSingleLevelBelow S B n P hm).inv.val.app U
        (systemModelTmul (S (B.map (homOfLE hm).op)).model P U 1 x)) =
      g.val.app U ((systemSingleLevelBelow S B n P hm).inv.val.app U
        (systemModelTmul (S (B.map (homOfLE hm).op)).model P U 1 x))) : f = g := by
  by_cases hm : m ≤ n
  · apply (cancel_epi (systemSingleLevelBelow S B n P hm).inv).1
    apply systemScalarModel_hom_ext (S (B.map (homOfLE hm).op))
    intro U x
    exact h hm U x
  · exact (systemSingleLevelAbove S B n P (Nat.lt_of_not_ge hm)).eq_of_src f g

/-- The identity transition of ordinary singleton extension is the identity on sections.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension).
Proof: compare the transition with inverse scalar restriction along the identity. Their
values on unit tensors agree by the transition formula. Unit tensors detect maps below n,
and the source is zero above n. -/
theorem systemSingleTransition_identity (P : systemLevel B n) (m : ℕ) (U : Cᵒᵖ)
    (x : (systemSingleLevel S B n P m).val.obj U) :
    (systemSingleTransition S T B n P (Nat.le_refl m)).val.app U x = x := by
  let η := systemScalarRestrictionUnit (B.map (homOfLE (Nat.le_refl m)).op)
    (B.map_id (op m))
  have he : systemSingleTransition S T B n P (Nat.le_refl m) =
      η.inv.app (systemSingleLevel S B n P m) := by
    apply systemSingleLevel_hom_ext S B n P m
    intro hm V y
    change (systemSingleTransition S T B n P (Nat.le_refl m)).val.app V _ =
      (systemSingleLevelBelow S B n P hm).inv.val.app V
        (systemModelTmul (S (B.map (homOfLE hm).op)).model P V 1 y)
    simpa only [map_one] using
      systemSingleTransition_tmul S T B n P (Nat.le_refl m) hm V 1 y
  exact congrArg (fun f ↦ f.val.app U x) he

/-- Singleton-extension transitions compose on all sections.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension).
Proof: insert the canonical identity-on-sections restriction compositor. Compare the
composite and direct transition on unit tensors: both send one tensor x to one tensor x.
The tensor-generator criterion, including its zero-source case, gives equality of the
module-sheaf maps; evaluation gives the asserted section equality. -/
theorem systemSingleTransition_compose (P : systemLevel B n) {l m k : ℕ}
    (h : l ≤ m) (q : m ≤ k) (U : Cᵒᵖ)
    (x : (systemSingleLevel S B n P k).val.obj U) :
    (systemSingleTransition S T B n P (h.trans q)).val.app U x =
      (systemSingleTransition S T B n P h).val.app U
        ((systemSingleTransition S T B n P q).val.app U x) := by
  have hc : B.map (homOfLE (h.trans q)).op =
      B.map (homOfLE q).op ≫ B.map (homOfLE h).op := by
    rw [← B.map_comp]
    rfl
  let η := systemScalarRestrictionComposition _ _ _ hc
  have he : systemSingleTransition S T B n P (h.trans q) =
      systemSingleTransition S T B n P q ≫
        (systemRestriction B q).map (systemSingleTransition S T B n P h) ≫
        η.hom.app (systemSingleLevel S B n P l) := by
    apply systemSingleLevel_hom_ext S B n P k
    intro hk V y
    change (systemSingleTransition S T B n P (h.trans q)).val.app V _ =
      (systemSingleTransition S T B n P h).val.app V
        ((systemSingleTransition S T B n P q).val.app V
          ((systemSingleLevelBelow S B n P hk).inv.val.app V
            (systemModelTmul (S (B.map (homOfLE hk).op)).model P V 1 y)))
    rw [systemSingleTransition_tmul, systemSingleTransition_tmul]
    simp only [map_one]
    rw [systemSingleTransition_tmul]
    simp only [map_one]
    rfl
  exact congrArg (fun f ↦ f.val.app U x) he

/-- The strict system underlying extension from the singleton level.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension). -/
def systemSingleObject (P : systemLevel B n) : StrictRingSystem B where
  level := systemSingleLevel S B n P
  transition := systemSingleTransition S T B n P
  identity := systemSingleTransition_identity S T B n P
  compose := systemSingleTransition_compose S T B n P

/-- Extension of a module map at one ordinary singleton level.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension). -/
def systemSingleMapLevel {P Q : systemLevel B n} (f : P ⟶ Q) (m : ℕ) :
    systemSingleLevel S B n P m ⟶ systemSingleLevel S B n Q m :=
  if hm : m ≤ n then
    (systemSingleLevelBelow S B n P hm).hom ≫ (systemTensor S B hm).map f ≫
      (systemSingleLevelBelow S B n Q hm).inv
  else 0

/-- A singleton-extension map preserves local tensors in below-level coordinates.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension).
Proof: the branch is scalar extension of f, conjugated by the level identifications.
Cancel the identifications and apply naturality of local tensors. -/
theorem systemSingleMapLevel_tmul {P Q : systemLevel B n} (f : P ⟶ Q) {m : ℕ}
    (hm : m ≤ n) (U : Cᵒᵖ) (c : (B.obj (op m)).obj.obj U) (x : P.val.obj U) :
    (systemSingleMapLevel S B n f m).val.app U
      ((systemSingleLevelBelow S B n P hm).inv.val.app U
        (systemModelTmul (S (B.map (homOfLE hm).op)).model P U c x)) =
    (systemSingleLevelBelow S B n Q hm).inv.val.app U
      (systemModelTmul (S (B.map (homOfLE hm).op)).model Q U c (f.val.app U x)) := by
  have he : (systemSingleLevelBelow S B n P hm).inv ≫ systemSingleMapLevel S B n f m =
      (systemTensor S B hm).map f ≫ (systemSingleLevelBelow S B n Q hm).inv := by
    dsimp only [systemSingleMapLevel]
    rw [dite_eq_left hm]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have ht := congrArg (fun t ↦ t.val.app U
    (systemModelTmul (S (B.map (homOfLE hm).op)).model P U c x)) he
  change (systemSingleMapLevel S B n f m).val.app U
      ((systemSingleLevelBelow S B n P hm).inv.val.app U _) =
    (systemSingleLevelBelow S B n Q hm).inv.val.app U
      (((systemTensor S B hm).map f).val.app U _) at ht
  rw [systemScalarModel_map_tmul] at ht
  exact ht

/-- Extension of a module morphism commutes with every strict transition.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension).
Proof: test on local unit tensors; the map applies f to x and the transition changes
one scalar to one, in either order. The zero-level case follows from uniqueness of
maps out of zero. -/
theorem systemSingleMap_comm {P Q : systemLevel B n} (f : P ⟶ Q)
    {l m : ℕ} (h : l ≤ m) :
    systemSingleMapLevel S B n f m ≫ systemSingleTransition S T B n Q h =
      systemSingleTransition S T B n P h ≫
        (systemRestriction B h).map (systemSingleMapLevel S B n f l) := by
  apply systemSingleLevel_hom_ext S B n P m
  intro hm U x
  change (systemSingleTransition S T B n Q h).val.app U
      ((systemSingleMapLevel S B n f m).val.app U _) =
    (systemSingleMapLevel S B n f l).val.app U
      ((systemSingleTransition S T B n P h).val.app U _)
  rw [systemSingleMapLevel_tmul, systemSingleTransition_tmul,
    systemSingleTransition_tmul, systemSingleMapLevel_tmul]

/-- Ordinary singleton extension as an actual functor of strict systems.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension). -/
def systemSingleFunctor : systemLevel B n ⥤ StrictRingSystem B where
  obj := systemSingleObject S T B n
  map f := { app := systemSingleMapLevel S B n f, comm := systemSingleMap_comm S T B n f }
  map_id P := by
    apply strictRingSystem_hom_ext B
    intro m
    apply systemSingleLevel_hom_ext S B n P m
    intro hm U x
    change (systemSingleMapLevel S B n (𝟙 P) m).val.app U _ = _
    rw [systemSingleMapLevel_tmul]
    rfl
  map_comp {P Q R} f g := by
    apply strictRingSystem_hom_ext B
    intro m
    apply systemSingleLevel_hom_ext S B n P m
    intro hm U x
    change (systemSingleMapLevel S B n (f ≫ g) m).val.app U _ =
      (systemSingleMapLevel S B n g m).val.app U
        ((systemSingleMapLevel S B n f m).val.app U _)
    rw [systemSingleMapLevel_tmul, systemSingleMapLevel_tmul, systemSingleMapLevel_tmul]
    rfl

/-- Ordinary singleton extension is naturally the prescribed tensor functor below n.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension). -/
def systemSingleBelow {m : ℕ} (h : m ≤ n) :
    systemSingleFunctor S T B n ⋙ systemEvaluation B m ≅ systemTensor S B h :=
  NatIso.ofComponents (fun P ↦ systemSingleLevelBelow S B n P h) (by
    intro P Q f
    dsimp only [systemSingleMapLevel, systemSingleFunctor, Functor.comp_map,
      systemEvaluation]
    rw [dite_eq_left h]
    erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The unit map inserts a local unit tensor at level n.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension). -/
def systemSingleUnit (P : systemLevel B n) :
    P ⟶ (systemSingleObject S T B n P).level n :=
  (T.ordinaryUnit B n).inv.app P ≫
    (systemSingleLevelBelow S B n P (Nat.le_refl n)).inv

/-- The scalar-unit inverse is the local unit tensor.
Source: Stacks 03EK (blueprint: lem-pur-system-ordinary-single-extension).
Proof: apply the tensor unitor to both sides. Its normalized multiplication formula
sends one tensor x to x, while the inverse unitor cancels against the unitor. -/
theorem systemTensorUnit_inv_tmul (P : systemLevel B n) (U : Cᵒᵖ) (x : P.val.obj U) :
    ((T.ordinaryUnit B n).inv.app P).val.app U x =
      systemModelTmul (S (B.map (homOfLE (Nat.le_refl n)).op)).model P U 1 x := by
  have hinj : Function.Injective (((T.ordinaryUnit B n).hom.app P).val.app U) := by
    apply Function.LeftInverse.injective
      (g := fun z ↦ ((T.ordinaryUnit B n).inv.app P).val.app U z)
    intro z
    exact congrArg (fun t ↦ t.val.app U z) ((T.ordinaryUnit B n).hom_inv_id_app P)
  apply hinj
  have hi := congrArg (fun t ↦ t.val.app U x) ((T.ordinaryUnit B n).inv_hom_id_app P)
  change ((T.ordinaryUnit B n).hom.app P).val.app U
    (((T.ordinaryUnit B n).inv.app P).val.app U x) = x at hi
  rw [hi, T.unit_normalized, one_smul]

/-- The singleton unit in coordinates is exactly one tensor x.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension).
Proof: apply the scalar-unit inverse formula before the below-level coordinate map. -/
theorem systemSingleUnit_tmul (P : systemLevel B n) (U : Cᵒᵖ) (x : P.val.obj U) :
    (systemSingleUnit S T B n P).val.app U x =
      (systemSingleLevelBelow S B n P (Nat.le_refl n)).inv.val.app U
        (systemModelTmul (S (B.map (homOfLE (Nat.le_refl n)).op)).model P U 1 x) := by
  change (systemSingleLevelBelow S B n P (Nat.le_refl n)).inv.val.app U
    (((T.ordinaryUnit B n).inv.app P).val.app U x) = _
  rw [systemTensorUnit_inv_tmul]

/-- A map to the nth component extends to all lower levels by scalar transposition.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension). -/
def systemSingleAdjunctLevel (P : systemLevel B n) (M : StrictRingSystem B)
    (f : P ⟶ M.level n) (m : ℕ) : systemSingleLevel S B n P m ⟶ M.level m :=
  if hm : m ≤ n then
    (systemSingleLevelBelow S B n P hm).hom ≫
      ((systemTensorAdj S B hm).homEquiv P (M.level m)).symm (f ≫ M.transition hm)
  else 0

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The extended map sends c tensor x to c times the actual transition of f(x).
Source: Zheng 4.1; Stacks 03D7
(blueprint: lem-pur-system-ordinary-single-extension).
Proof: in below-level coordinates cancel the coordinate isomorphisms. The scalar
transpose formula and the inverse law for the Hom bijection give the result. -/
theorem systemSingleAdjunctLevel_tmul (P : systemLevel B n) (M : StrictRingSystem B)
    (f : P ⟶ M.level n) {m : ℕ} (hm : m ≤ n) (U : Cᵒᵖ)
    (c : (B.obj (op m)).obj.obj U) (x : P.val.obj U) :
    (systemSingleAdjunctLevel S B n P M f m).val.app U
      ((systemSingleLevelBelow S B n P hm).inv.val.app U
        (systemModelTmul (S (B.map (homOfLE hm).op)).model P U c x)) =
    c • (show (M.level m).val.obj U from
      (M.transition hm).val.app U (f.val.app U x)) := by
  have he : (systemSingleLevelBelow S B n P hm).inv ≫
      systemSingleAdjunctLevel S B n P M f m =
      ((systemTensorAdj S B hm).homEquiv P (M.level m)).symm (f ≫ M.transition hm) := by
    dsimp only [systemSingleAdjunctLevel]
    rw [dite_eq_left hm]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have ht := congrArg (fun t ↦ t.val.app U
    (systemModelTmul (S (B.map (homOfLE hm).op)).model P U c x)) he
  change (systemSingleAdjunctLevel S B n P M f m).val.app U
      ((systemSingleLevelBelow S B n P hm).inv.val.app U _) = _ at ht
  rw [systemScalarModel_transpose_tmul (S (B.map (homOfLE hm).op)) P (M.level m)
    (((systemTensorAdj S B hm).homEquiv P (M.level m)).symm (f ≫ M.transition hm)),
    Equiv.apply_symm_apply] at ht
  exact ht

/-- The transposed component maps are a strict system map.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension).
Proof: on one tensor x, the two paths are the direct transition of f(x) and the two
successive transitions of f(x); these agree by the strict composition law of M. -/
theorem systemSingleAdjunct_comm (P : systemLevel B n) (M : StrictRingSystem B)
    (f : P ⟶ M.level n) {l m : ℕ} (h : l ≤ m) :
    systemSingleAdjunctLevel S B n P M f m ≫ M.transition h =
      systemSingleTransition S T B n P h ≫
        (systemRestriction B h).map (systemSingleAdjunctLevel S B n P M f l) := by
  apply systemSingleLevel_hom_ext S B n P m
  intro hm U x
  change (M.transition h).val.app U
      ((systemSingleAdjunctLevel S B n P M f m).val.app U _) =
    (systemSingleAdjunctLevel S B n P M f l).val.app U
      ((systemSingleTransition S T B n P h).val.app U _)
  rw [systemSingleAdjunctLevel_tmul, one_smul, systemSingleTransition_tmul,
    map_one, systemSingleAdjunctLevel_tmul, one_smul]
  exact (M.compose h hm U (f.val.app U x)).symm

/-- Extend a map to the selected component into a map of strict systems.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension). -/
def systemSingleAdjunct (P : systemLevel B n) (M : StrictRingSystem B)
    (f : P ⟶ M.level n) : systemSingleObject S T B n P ⟶ M where
  app := systemSingleAdjunctLevel S B n P M f
  comm := systemSingleAdjunct_comm S T B n P M f

/-- Taking the selected component of the extension of f recovers f.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension).
Proof: the unit is one tensor x; its image is the identity transition applied to f(x),
which is f(x). -/
theorem systemSingleAdjunct_right_inv (P : systemLevel B n) (M : StrictRingSystem B)
    (f : P ⟶ M.level n) :
    systemSingleUnit S T B n P ≫ (systemSingleAdjunct S T B n P M f).app n = f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change (systemSingleAdjunctLevel S B n P M f n).val.app U
    ((systemSingleUnit S T B n P).val.app U x) = f.val.app U x
  rw [systemSingleUnit_tmul, systemSingleAdjunctLevel_tmul, one_smul, M.identity]

/-- Every map from singleton extension is determined by its unit at the selected level.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension).
Proof: the strict-map square for n to m, evaluated on the unit tensor, identifies the
mth component with the transition of the nth component. Those are exactly the scalar
adjunct component formulas. Unit tensors detect maps below n and maps out of zero agree
above n. -/
theorem systemSingleAdjunct_left_inv (P : systemLevel B n) (M : StrictRingSystem B)
    (f : systemSingleObject S T B n P ⟶ M) :
    systemSingleAdjunct S T B n P M (systemSingleUnit S T B n P ≫ f.app n) = f := by
  apply strictRingSystem_hom_ext B
  intro m
  apply systemSingleLevel_hom_ext S B n P m
  intro hm U x
  change (systemSingleAdjunctLevel S B n P M _ m).val.app U _ = (f.app m).val.app U _
  rw [systemSingleAdjunctLevel_tmul, one_smul]
  have he := congrArg (fun t ↦ t.val.app U ((systemSingleUnit S T B n P).val.app U x))
    (f.comm hm)
  change (M.transition hm).val.app U
      ((f.app n).val.app U ((systemSingleUnit S T B n P).val.app U x)) =
    (f.app m).val.app U
      ((systemSingleTransition S T B n P hm).val.app U
        ((systemSingleUnit S T B n P).val.app U x)) at he
  rw [systemSingleUnit_tmul, systemSingleTransition_tmul, map_one] at he
  change (M.transition hm).val.app U
      ((f.app n).val.app U ((systemSingleUnit S T B n P).val.app U x)) = _
  rw [systemSingleUnit_tmul]
  exact he

/-- The ordinary singleton left-extension adjunction, with its strict transpose.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension). -/
def systemSingleAdjunction : systemSingleFunctor S T B n ⊣ systemEvaluation B n :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P M ↦
        { toFun := fun f ↦ systemSingleUnit S T B n P ≫ f.app n
          invFun := systemSingleAdjunct S T B n P M
          left_inv := systemSingleAdjunct_left_inv S T B n P M
          right_inv := systemSingleAdjunct_right_inv S T B n P M }
      homEquiv_naturality_left_symm := by
        intro P Q M f g
        apply strictRingSystem_hom_ext B
        intro m
        apply systemSingleLevel_hom_ext S B n P m
        intro hm U x
        change (systemSingleAdjunctLevel S B n P M (f ≫ g) m).val.app U _ =
          (systemSingleAdjunctLevel S B n Q M g m).val.app U
            ((systemSingleMapLevel S B n f m).val.app U _)
        rw [systemSingleMapLevel_tmul, systemSingleAdjunctLevel_tmul, one_smul]
        erw [systemSingleAdjunctLevel_tmul, one_smul]
        rfl
      homEquiv_naturality_right := by
        intro P M N f g
        change systemSingleUnit S T B n P ≫ (f.app n ≫ g.app n) =
          (systemSingleUnit S T B n P ≫ f.app n) ≫ g.app n
        exact (Category.assoc _ _ _).symm }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Singleton extension is additive, as is already visible on tensor coordinates.
Source: Zheng 4.1 (blueprint: lem-pur-system-ordinary-single-extension). -/
instance systemSingleFunctorAdditive : (systemSingleFunctor S T B n).Additive where
  map_add := by
    intro P Q f g
    apply strictRingSystem_hom_ext B
    intro m
    have he := (systemEvaluation B m).map_add
      (f := (systemSingleFunctor S T B n).map f)
      (g := (systemSingleFunctor S T B n).map g)
    change systemSingleMapLevel S B n (f + g) m = _
    apply Eq.trans (b := systemSingleMapLevel S B n f m + systemSingleMapLevel S B n g m)
    · by_cases hm : m ≤ n
      · dsimp only [systemSingleMapLevel]
        rw [dite_eq_left hm, dite_eq_left hm, dite_eq_left hm]
        rw [(systemTensor S B hm).map_add, Preadditive.add_comp, Preadditive.comp_add]
      · dsimp only [systemSingleMapLevel]
        rw [dite_eq_right hm, dite_eq_right hm, dite_eq_right hm, zero_add]
    · exact he.symm

/-- The ordinary below-level formula intertwines the two actual adjunction transposes.
Source: Zheng 4.1; Stacks 03D7
(blueprint: lem-pur-system-ordinary-single-extension).
Proof: evaluate the scalar transpose on x using its unit tensor. The strict-map
square from n to m and the singleton unit identify the result with the nth transpose
followed by the strict transition. -/
theorem systemSingleTranspose {m : ℕ} (h : m ≤ n) (P : systemLevel B n)
    (M : StrictRingSystem B) (f : (systemSingleFunctor S T B n).obj P ⟶ M) :
    (systemTensorAdj S B h).homEquiv P (M.level m)
      ((systemSingleBelow S T B n h).inv.app P ≫ f.app m) =
    (systemSingleAdjunction S T B n).homEquiv P M f ≫ M.transition h := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  rw [Adjunction.homEquiv_unit]
  change (f.app m).val.app U
      ((systemSingleLevelBelow S B n P h).inv.val.app U
        (((S (B.map (homOfLE h).op)).ordinaryAdj.unit.app P).val.app U x)) =
    (M.transition h).val.app U
      ((f.app n).val.app U ((systemSingleUnit S T B n P).val.app U x))
  rw [(S (B.map (homOfLE h).op)).unit_normalized]
  have he := congrArg (fun t ↦ t.val.app U ((systemSingleUnit S T B n P).val.app U x))
    (f.comm h)
  change (M.transition h).val.app U
      ((f.app n).val.app U ((systemSingleUnit S T B n P).val.app U x)) =
    (f.app m).val.app U
      ((systemSingleTransition S T B n P h).val.app U
        ((systemSingleUnit S T B n P).val.app U x)) at he
  rw [systemSingleUnit_tmul, systemSingleTransition_tmul, map_one] at he
  rw [systemSingleUnit_tmul]
  exact he.symm

end SheafOfModules
