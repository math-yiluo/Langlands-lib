/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.ModuleInverseImageAction
public import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
/-! # Constructing scalar actions from set inverse-image presentations
Source: Stacks Project, Modules on Sites, Tag 03D2.
(auxiliary; not a blueprint node).
-/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.sheafPullbackConstruction
namespace SheafOfModules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  [PreservesFiniteLimits (sheafPullback F (Type u) J K)]
  {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}}
  (φ : A ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj B)
  (M : SheafOfModules.{u} A)
/-- Transport the scalar operation, and test each module law on products of unit sections.
Source: Stacks Project, Tag 03D2.
(auxiliary; not a blueprint node).
Proof: transport the source scalar-action morphism using the product of the two
presentations. Naturality gives semilinear restrictions. Its defining equation on
units gives unit linearity. Each module axiom is an equality of sheaf maps out of a
product of one, two or three of the given presentations. Test on source-unit tuples;
the ring unit preserves addition, multiplication, zero and one, and the abelian unit
preserves addition and zero. The equations reduce to the source module axioms. -/
theorem inverseImageAction_of_presentations
    (pr : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (CategoryTheory.forget RingCat.{u})).obj A)
      ((sheafCompose K (CategoryTheory.forget RingCat.{u})).obj B))
    (hr : pr.unit = (sheafCompose J (CategoryTheory.forget RingCat.{u})).map φ)
    (pa : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj ((toSheaf A).obj M))
      ((sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
        ((sheafPullback F AddCommGrpCat.{u} J K).obj ((toSheaf A).obj M))))
    (ha : pa.unit = (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).map
      ((sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app ((toSheaf A).obj M))) :
    Nonempty (InverseImageAction φ M) := by
  let N := (sheafPullback F AddCommGrpCat.{u} J K).obj ((toSheaf A).obj M)
  let R := (sheafCompose K (CategoryTheory.forget RingCat.{u})).obj B
  let T := (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj N
  let mu0 : (sheafCompose J (CategoryTheory.forget RingCat.{u})).obj A ⊗
      (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj ((toSheaf A).obj M) ⟶
      (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj ((toSheaf A).obj M) :=
    ⟨{ app := fun U ↦ ↾fun x ↦
         @SMul.smul (A.obj.obj U) (M.val.obj U) inferInstance x.1 x.2
       naturality := by
         intro U V i
         ext x
         exact (M.val.map_smul i x.1 x.2).symm }⟩
  let mu : R ⊗ T ⟶ T := (pr.tensor pa).map pa mu0
  let act (U : Dᵒᵖ) (r : B.obj.obj U) (m : N.obj.obj U) : N.obj.obj U := mu.hom.app U (r, m)
  have hn {U V : Dᵒᵖ} (i : U ⟶ V) (r : B.obj.obj U) (m : N.obj.obj U) :
      N.obj.map i (act U r m) = act V (B.obj.map i r) (N.obj.map i m) :=
    by
      have h := mu.hom.naturality i
      have h' := ConcreteCategory.congr_hom h (show (R ⊗ T).obj.obj U from (r, m))
      exact h'.symm
  let η := (sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app ((toSheaf A).obj M)
  have hu (U : Cᵒᵖ) (r : A.obj.obj U) (m : M.val.obj U) :
      act (F.op.obj U) (φ.hom.app U r) (η.hom.app U m) = η.hom.app U (r • m) := by
    have h := (pr.tensor pa).map_unit pa mu0 U (r, m)
    change act (F.op.obj U) (pr.unit.hom.app U r) (pa.unit.hom.app U m) =
      pa.unit.hom.app U (r • m) at h
    rw [hr, ha] at h
    exact h
  have hone : ∀ U m, act U 1 m = m := by
    let a : T ⟶ T :=
      ⟨{ app := fun U ↦ ↾fun m ↦ act U 1 m
         naturality := by
           intro U V i
           ext m
           change act V 1 (N.obj.map i m) = N.obj.map i (act U 1 m)
           rw [hn, map_one] }⟩
    have h := pa.hom_ext a (𝟙 T) (by
      intro U m
      rw [ha]
      change act (F.op.obj U) 1 (η.hom.app U m) = η.hom.app U m
      rw [← (φ.hom.app U).hom.map_one, hu, one_smul])
    intro U m
    exact congrArg (fun z ↦ z.hom.app U m) h
  have hzero : ∀ U m, act U 0 m = 0 := by
    let a : T ⟶ T :=
      ⟨{ app := fun U ↦ ↾fun m ↦ act U 0 m
         naturality := by
           intro U V i
           ext m
           change act V 0 (N.obj.map i m) = N.obj.map i (act U 0 m)
           rw [hn, map_zero] }⟩
    let b : T ⟶ T :=
      ⟨{ app := fun U ↦ ↾fun _ ↦ (0 : N.obj.obj U)
         naturality := by
           intro U V i
           ext m
           change (0 : N.obj.obj V) = N.obj.map i 0
           exact (N.obj.map i).hom.map_zero.symm }⟩
    have h := pa.hom_ext a b (by
      intro U m
      rw [ha]
      change act (F.op.obj U) 0 (η.hom.app U m) = 0
      rw [← (φ.hom.app U).hom.map_zero, hu, zero_smul, (η.hom.app U).hom.map_zero])
    intro U m
    exact congrArg (fun z ↦ z.hom.app U m) h
  have hsmulzero : ∀ U r, act U r 0 = 0 := by
    let a : R ⟶ T :=
      ⟨{ app := fun U ↦ ↾fun r ↦ act U r 0
         naturality := by
           intro U V i
           ext r
           change act V (B.obj.map i r) 0 = N.obj.map i (act U r 0)
           rw [hn, (N.obj.map i).hom.map_zero] }⟩
    let b : R ⟶ T :=
      ⟨{ app := fun U ↦ ↾fun _ ↦ (0 : N.obj.obj U)
         naturality := by
           intro U V i
           ext r
           change (0 : N.obj.obj V) = N.obj.map i 0
           exact (N.obj.map i).hom.map_zero.symm }⟩
    have h := pr.hom_ext a b (by
      intro U r
      rw [hr]
      change act (F.op.obj U) (φ.hom.app U r) 0 = 0
      rw [← (η.hom.app U).hom.map_zero, hu, smul_zero, (η.hom.app U).hom.map_zero])
    intro U r
    exact congrArg (fun z ↦ z.hom.app U r) h
  have hadd : ∀ U r m n, act U r (m + n) = act U r m + act U r n := by
    let a : R ⊗ (T ⊗ T) ⟶ T :=
      ⟨{ app := fun U ↦ ↾fun x ↦
           act U x.1 ((show N.obj.obj U from x.2.1) + (show N.obj.obj U from x.2.2))
         naturality := by
           intro U V i
           ext x
           change act V (B.obj.map i x.1)
             (N.obj.map i x.2.1 + N.obj.map i x.2.2) =
               N.obj.map i (act U x.1
                 ((show N.obj.obj U from x.2.1) + (show N.obj.obj U from x.2.2)))
           rw [hn, (N.obj.map i).hom.map_add] }⟩
    let b : R ⊗ (T ⊗ T) ⟶ T :=
      ⟨{ app := fun U ↦ ↾fun x ↦ act U x.1 x.2.1 + act U x.1 x.2.2
         naturality := by
           intro U V i
           ext x
           change act V (B.obj.map i x.1) (N.obj.map i x.2.1) +
             act V (B.obj.map i x.1) (N.obj.map i x.2.2) =
               N.obj.map i (act U x.1 x.2.1 + act U x.1 x.2.2)
           rw [(N.obj.map i).hom.map_add, hn, hn] }⟩
    have h := (pr.tensor (pa.tensor pa)).hom_ext a b (by
      intro U x
      change act (F.op.obj U) (pr.unit.hom.app U x.1)
        ((show N.obj.obj (F.op.obj U) from pa.unit.hom.app U x.2.1) +
          (show N.obj.obj (F.op.obj U) from pa.unit.hom.app U x.2.2)) =
          act (F.op.obj U) (pr.unit.hom.app U x.1) (pa.unit.hom.app U x.2.1) +
          act (F.op.obj U) (pr.unit.hom.app U x.1) (pa.unit.hom.app U x.2.2)
      rw [hr, ha]
      change act (F.op.obj U) (φ.hom.app U x.1)
        (η.hom.app U x.2.1 + η.hom.app U x.2.2) =
          act (F.op.obj U) (φ.hom.app U x.1) (η.hom.app U x.2.1) +
          act (F.op.obj U) (φ.hom.app U x.1) (η.hom.app U x.2.2)
      rw [← (η.hom.app U).hom.map_add, hu, smul_add,
        (η.hom.app U).hom.map_add, hu, hu])
    intro U r m n
    exact congrArg (fun z ↦ z.hom.app U (r, m, n)) h
  have hscalaradd : ∀ U r s m, act U (r + s) m = act U r m + act U s m := by
    let a : R ⊗ (R ⊗ T) ⟶ T :=
      ⟨{ app := fun U ↦ ↾fun x ↦
           act U ((show B.obj.obj U from x.1) + (show B.obj.obj U from x.2.1)) x.2.2
         naturality := by
           intro U V i
           ext x
           change act V (B.obj.map i x.1 + B.obj.map i x.2.1) (N.obj.map i x.2.2) =
             N.obj.map i (act U ((show B.obj.obj U from x.1) + (show B.obj.obj U from x.2.1)) x.2.2)
           rw [hn, (B.obj.map i).hom.map_add] }⟩
    let b : R ⊗ (R ⊗ T) ⟶ T :=
      ⟨{ app := fun U ↦ ↾fun x ↦ act U x.1 x.2.2 + act U x.2.1 x.2.2
         naturality := by
           intro U V i
           ext x
           change act V (B.obj.map i x.1) (N.obj.map i x.2.2) +
             act V (B.obj.map i x.2.1) (N.obj.map i x.2.2) =
               N.obj.map i (act U x.1 x.2.2 + act U x.2.1 x.2.2)
           rw [(N.obj.map i).hom.map_add, hn, hn] }⟩
    have h := (pr.tensor (pr.tensor pa)).hom_ext a b (by
      intro U x
      change act (F.op.obj U) ((show B.obj.obj (F.op.obj U) from pr.unit.hom.app U x.1) +
        (show B.obj.obj (F.op.obj U) from pr.unit.hom.app U x.2.1))
        ((show N.obj.obj (F.op.obj U) from pa.unit.hom.app U x.2.2)) =
          act (F.op.obj U) (pr.unit.hom.app U x.1) (pa.unit.hom.app U x.2.2) +
          act (F.op.obj U) (pr.unit.hom.app U x.2.1) (pa.unit.hom.app U x.2.2)
      rw [hr, ha]
      change act (F.op.obj U) (φ.hom.app U x.1 + φ.hom.app U x.2.1)
        (η.hom.app U x.2.2) =
          act (F.op.obj U) (φ.hom.app U x.1) (η.hom.app U x.2.2) +
          act (F.op.obj U) (φ.hom.app U x.2.1) (η.hom.app U x.2.2)
      rw [← (φ.hom.app U).hom.map_add, hu, add_smul,
        (η.hom.app U).hom.map_add, hu, hu])
    intro U r s m
    exact congrArg (fun z ↦ z.hom.app U (r, s, m)) h
  have hmul : ∀ U r s m, act U (r * s) m = act U r (act U s m) := by
    let a : R ⊗ (R ⊗ T) ⟶ T :=
      ⟨{ app := fun U ↦ ↾fun x ↦
           act U ((show B.obj.obj U from x.1) * (show B.obj.obj U from x.2.1)) x.2.2
         naturality := by
           intro U V i
           ext x
           change act V (B.obj.map i x.1 * B.obj.map i x.2.1) (N.obj.map i x.2.2) =
             N.obj.map i (act U ((show B.obj.obj U from x.1) * (show B.obj.obj U from x.2.1)) x.2.2)
           rw [hn, (B.obj.map i).hom.map_mul] }⟩
    let b : R ⊗ (R ⊗ T) ⟶ T :=
      ⟨{ app := fun U ↦ ↾fun x ↦ act U x.1 (act U x.2.1 x.2.2)
         naturality := by
           intro U V i
           ext x
           change act V (B.obj.map i x.1)
             (act V (B.obj.map i x.2.1) (N.obj.map i x.2.2)) =
               N.obj.map i (act U x.1 (act U x.2.1 x.2.2))
           rw [hn, hn] }⟩
    have h := (pr.tensor (pr.tensor pa)).hom_ext a b (by
      intro U x
      change act (F.op.obj U) ((show B.obj.obj (F.op.obj U) from pr.unit.hom.app U x.1) *
        (show B.obj.obj (F.op.obj U) from pr.unit.hom.app U x.2.1))
        ((show N.obj.obj (F.op.obj U) from pa.unit.hom.app U x.2.2)) =
          act (F.op.obj U) (pr.unit.hom.app U x.1)
            (act (F.op.obj U) (pr.unit.hom.app U x.2.1) (pa.unit.hom.app U x.2.2))
      rw [hr, ha]
      change act (F.op.obj U) (φ.hom.app U x.1 * φ.hom.app U x.2.1)
        (η.hom.app U x.2.2) =
          act (F.op.obj U) (φ.hom.app U x.1)
            (act (F.op.obj U) (φ.hom.app U x.2.1) (η.hom.app U x.2.2))
      rw [← (φ.hom.app U).hom.map_mul, hu, hu, hu, mul_smul])
    intro U r s m
    exact congrArg (fun z ↦ z.hom.app U (r, s, m)) h
  let modules (U : Dᵒᵖ) : Module (B.obj.obj U) (N.obj.obj U) :=
    { smul := act U
      one_smul := hone U
      mul_smul := hmul U
      smul_zero := hsmulzero U
      smul_add := hadd U
      add_smul := hscalaradd U
      zero_smul := hzero U }
  exact ⟨⟨modules, hn, fun U r m ↦ (hu U r m).symm⟩⟩
end SheafOfModules
