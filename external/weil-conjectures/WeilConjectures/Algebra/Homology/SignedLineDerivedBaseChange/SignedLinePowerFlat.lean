/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChangeData
import all WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

/-! # Flatness of signed powers of locally trivial lines -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules.SignedLineDerivedBaseChange
attribute [local irreducible] monoidalCategory siteSheafTensorRight
attribute [local instance 2000] cochainModulesMonoidal
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  (A : Sheaf J CommRingCat.{max u v w})

private def chart_restrict (M : KFlatFixedTensor.Modules A) {V W : C}
    (e : M.over V ≅ unit
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).over V)) (f : W ⟶ V) :
    M.over W ≅ unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).over W) where
  hom := ⟨{ app := fun Z ↦ e.hom.val.app (op ((Over.map f).obj Z.unop))
            naturality := by
              intro Z Z' g
              exact e.hom.val.naturality ((Over.map f).op.map g) }⟩
  inv := ⟨{ app := fun Z ↦ e.inv.val.app (op ((Over.map f).obj Z.unop))
            naturality := by
              intro Z Z' g
              exact e.inv.val.naturality ((Over.map f).op.map g) }⟩
  hom_inv_id := by
    ext Z x
    exact congrArg (fun h ↦ h.val.app (op ((Over.map f).obj Z.unop)) x) e.hom_inv_id
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro Z
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun h ↦ h.val.app (op ((Over.map f).obj Z.unop)) x) e.inv_hom_id

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}] in
private theorem chart_sieve (M : KFlatFixedTensor.Modules A)
    (hM : ∃ (I : Type u) (V : I → C), J.CoversTop V ∧ ∀ i,
      Nonempty (M.over (V i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).over (V i)))) :
    ∀ U : C, ∃ s : Sieve U, s ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), s f →
      Nonempty (M.over V ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).over V)) := by
  obtain ⟨I, V, hV, hM⟩ := hM
  intro U
  refine ⟨Sieve.ofObjects V U, hV U, ?_⟩
  rintro W f ⟨i, ⟨g⟩⟩
  exact ⟨chart_restrict A M (hM i).some g⟩

/-- Every signed power of a locally trivial line is flat.
Source: Stacks Project, Modules on Sites, Tags 03EL and 0B8Q.
(blueprint: lem-pur-signed-line-power-flat)
Proof: on each given line chart, induction identifies every positive tensor power with
the unit. Restriction commutes with the specified site tensor. Tensor isomorphisms and
the right unitor identify the induction step with the unit. These charts give a covering
sieve over every object. The evaluation-inverse-pair theorem then proves flatness both
of the positive power and its internal dual. These are exactly the two constructors of
the signed power. The argument also covers degree zero, zero rings and empty covers. -/
theorem signed_line_power_flat
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (P : KFlatFixedTensor.Modules A)
    (hP : ∃ (I : Type u) (V : I → C), J.CoversTop V ∧ ∀ i,
      Nonempty (P.over (V i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).over (V i))))
    (d : ℤ) : IsFlatOnSite (R := A) (signedLinePower.{u, v, w} P d) := by
  obtain ⟨I, V, hV, hP⟩ := hP
  have hc (i : I) : ∀ n : ℕ, (scalarTensorPower A P n).over (V i) ≅
      unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).over (V i)) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => exact Iso.refl _
    | one => exact (hP i).some
    | more n _ ih =>
      let c := (exists_localizedSiteTensorRestriction J A (V i)).choose
      let := monoidalCategory (A.over (V i))
      let X := (scalarTensorPower A P (n + 1)).over (V i)
      let Y := P.over (V i)
      exact c (scalarTensorPower A P (n + 1)) P ≪≫
        (siteSheafTensorRightIso (A.over (V i)) Y).app X ≪≫
          @MonoidalCategory.tensorIso _ _ (monoidalCategory (A.over (V i))) _ _ _ _
            ih (hP i).some ≪≫
          ((siteSheafTensorRightIso (A.over (V i)) (unit _)).app (unit _)).symm ≪≫
            scalarTensorRightUnitor (A.over (V i)) _
  have hs (n : ℕ) := chart_sieve A (scalarTensorPower A P n)
    ⟨I, V, hV, fun i ↦ ⟨hc i n⟩⟩
  cases d with
  | ofNat n =>
    exact (LineEvaluation.evaluation_inverse_pair_impl.{u, v, w} A (scalarTensorPower A P n) (hs n))
      |>.2.2.2.2.2.2.2.1
  | negSucc n =>
    exact (LineEvaluation.evaluation_inverse_pair_impl.{u, v, w} A
      (scalarTensorPower A P (n + 1)) (hs (n + 1)))
      |>.2.2.2.2.2.2.2.2.1

end SheafOfModules.SignedLineDerivedBaseChange
