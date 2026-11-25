/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
public import WeilConjectures.Algebra.Homology.System.SystemDerivedTransition

/-! # The actual derived transitions of strict systems

Source: Zheng, Construction 4.1; Stacks 015F.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- The identity coefficient restriction and its canonical derived unit comparison.
Source: Stacks 015F and 0FND
(blueprint: lem-pur-system-derived-transition-unit). -/
def systemDerivedRestrictionUnit (n : ℕ) :
    (systemRestriction B (Nat.le_refl n)).mapDerivedCategory ≅
      𝟭 (DerivedCategory (systemLevel B n)) :=
  Functor.exactDerivedRestrictionUnit _
    (systemScalarRestrictionUnit (B.map (homOfLE (Nat.le_refl n)).op) (B.map_id (op n)))

/-- The identity derived transition is the inverse identity-restriction comparison.
Source: Zheng 4.1; Stacks 015F
(blueprint: lem-pur-system-derived-transition-unit).
Proof: localization detects equality of natural transformations. On Q(K), postcompose
with the two invertible exact evaluation factorizations. The transition representative
formula and the inverse unit factorization identify both sides with Q of the strict
identity transition. Its equality to the ordinary restriction unit is checked on each
term and section using the strict system identity law. -/
theorem systemDerivedTransition_identity (n : ℕ)
    (M : DerivedCategory (StrictRingSystem B)) :
    (systemDerivedTransition B (Nat.le_refl n)).app M =
      (systemDerivedRestrictionUnit B n).inv.app ((derivedSystemEvaluation B n).obj M) := by
  let V := systemEvaluation B n
  let R := systemRestriction B (Nat.le_refl n)
  let η := systemScalarRestrictionUnit (B.map (homOfLE (Nat.le_refl n)).op) (B.map_id (op n))
  let ηc := NatIso.mapHomologicalComplex η (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (systemLevel B n) (.up ℤ)
  let δ := systemDerivedRestrictionUnit B n
  let σ : V.mapDerivedCategory ⟶ V.mapDerivedCategory ⋙ R.mapDerivedCategory :=
    (Functor.rightUnitor V.mapDerivedCategory).inv ≫
      Functor.whiskerLeft V.mapDerivedCategory δ.inv
  have he : systemDerivedTransition B (Nat.le_refl n) = σ := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ))
    intro K
    have hs : ((strictSystemTransition B (Nat.le_refl n)).mapHomologicalComplex (.up ℤ)).app K =
        ηc.inv.app ((V.mapHomologicalComplex (.up ℤ)).obj K) := by
      apply HomologicalComplex.hom_ext
      intro i
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      ext x
      exact (K.X i).identity n U x
    apply (cancel_mono (R.mapDerivedCategory.map (V.mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactors.hom.app ((V.mapHomologicalComplex (.up ℤ)).obj K))).1
    rw [systemDerivedTransition_rep]
    dsimp only [σ, NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app]
    erw [Category.id_comp]
    rw [← Category.assoc, ← δ.inv.naturality]
    dsimp only [Functor.id_map]
    rw [Category.assoc]
    change V.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map
        (((strictSystemTransition B (Nat.le_refl n)).mapHomologicalComplex (.up ℤ)).app K) =
      V.mapDerivedCategoryFactors.hom.app K ≫
        (δ.inv.app _ ≫ R.mapDerivedCategoryFactors.hom.app _)
    erw [Functor.exactDerivedRestrictionUnit_inv_fac R η]
    rw [hs]
  have hh := congrArg (fun τ ↦ τ.app M) he
  dsimp only [σ, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app] at hh
  erw [Category.id_comp] at hh
  exact hh

variable [EssentiallySmall.{w} C]

/-- The canonical derived tensor unit is the transpose of the actual identity transition.
Source: Zheng 4.1; Stacks 0FND
(blueprint: lem-pur-system-derived-transition-unit).
Proof: the canonical tensor unit is the left-adjoint uniqueness comparison with the
identity adjunction. Its transpose becomes the identity after the restriction unit
comparison, hence is the inverse of that comparison. The preceding theorem identifies
this inverse with the actual strict identity transition. -/
theorem systemDerivedTransition_tensorUnit
    (S : SystemScalarAssignment (J := J)) (n : ℕ)
    (M : DerivedCategory (StrictRingSystem B)) :
    ((systemDerivedTensorAdj S B (Nat.le_refl n)).homEquiv _ _).symm
      ((systemDerivedTransition B (Nat.le_refl n)).app M) =
    ((systemTensorCoherence S).derivedUnit B n).hom.app ((derivedSystemEvaluation B n).obj M) := by
  let A := S (B.map (homOfLE (Nat.le_refl n)).op)
  let δ := systemDerivedRestrictionUnit B n
  let X := (derivedSystemEvaluation B n).obj M
  have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (A.adjunction.ofNatIsoRight δ) Adjunction.id X
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at hu
  apply (Equiv.symm_apply_eq _).2
  rw [systemDerivedTransition_identity]
  apply (cancel_mono (δ.hom.app X)).1
  rw [Iso.inv_hom_id_app]
  exact hu.symm

end SheafOfModules
