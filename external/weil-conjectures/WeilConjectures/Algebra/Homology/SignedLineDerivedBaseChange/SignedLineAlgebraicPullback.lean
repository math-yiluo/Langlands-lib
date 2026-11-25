/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChangeData
public import WeilConjectures.CategoryTheory.SignedLinePullbackConstruction.SheafPullbackUnitPresentation.SignedLineSheafPullbackUnitPresentation
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence

/-! # The algebraic lift determined by pullback units -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
open CategoryTheory.SignedLinePullbackConstruction
namespace SheafOfModules.SignedLineDerivedBaseChange

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {R : Sheaf J CommRingCat.{max u v w}}
  {S : Sheaf K CommRingCat.{max u v w}}

/-- Unit-preserving presentations make the existing pullback an algebraic inverse image.
Source: Stacks Project, Modules on Sites, Tag 03D2.
(blueprint: lem-pur-signed-line-algebraic-pullback)
Proof: use the ring presentation and the natural module presentation for the underlying
isomorphisms. Ring addition and multiplication and module addition and scalar multiplication
are maps of sheaves of sets. Their compatibility on source units follows from the ring-map
and module-unit laws. The presentation adjunction tests equality on those units, so these
operations preserve every generalized graph. Zero follows from z = z + z by cancellation;
the constant-one graph follows by the same unit test. No choice of algebraic lift is used. -/
theorem algebraic_pullback_of_presentations
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    (pr : SheafPullbackUnitPresentation (F := U)
      ((sheafCompose J (CategoryTheory.forget CommRingCat)).obj R)
      ((sheafCompose K (CategoryTheory.forget CommRingCat)).obj S))
    (hr : pr.unit = (sheafCompose J (CategoryTheory.forget RingCat)).map a)
    (em : pull a ⋙ toSheaf _ ⋙ sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{max u v w}) ≅
      (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max u v w})) ⋙
        sheafPullback U (Type (max u v w)) J K)
    (he : ∀ (M : KFlatFixedTensor.Modules R) (V : Cᵒᵖ) (x : M.val.obj V),
      (em.hom.app M).hom.app (U.op.obj V)
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          M V.unop x) =
        ((sheafAdjunctionContinuous U (Type (max u v w)) J K).unit.app
          ((toSheaf _ ⋙ sheafCompose J
            (CategoryTheory.forget AddCommGrpCat.{max u v w})).obj M)).hom.app V x) :
    ∃ I : AlgebraicInverseImage (sheafPullback U (Type (max u v w)) J K) R S,
      I.modules = pull a ∧ I.ringUnderlying = pr.iso.symm ∧ HEq I.moduleUnderlying em := by
  let hm := module_pushforward_isRightAdjoint_of_universes a
  let := hm
  let pa (M : KFlatFixedTensor.Modules R) : SheafPullbackUnitPresentation (F := U)
      ((toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat)).obj M)
      ((toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat)).obj
        ((pull a).obj M)) :=
    { unit := (sheafCompose J (CategoryTheory.forget AddCommGrpCat)).map
        ((toSheaf _).map ((pullbackPushforwardAdjunction a).unit.app M))
      iso := em.app M
      equation := he M }
  let rAdd : ((sheafCompose K (CategoryTheory.forget CommRingCat)).obj S) ⊗
      ((sheafCompose K (CategoryTheory.forget CommRingCat)).obj S) ⟶
        (sheafCompose K (CategoryTheory.forget CommRingCat)).obj S :=
    ⟨{ app := fun W ↦ ↾fun x ↦ @Add.add (S.obj.obj W) inferInstance x.1 x.2
       naturality := by intro W W' f; ext x; exact ((S.obj.map f).hom.map_add _ _).symm }⟩
  let rMul : ((sheafCompose K (CategoryTheory.forget CommRingCat)).obj S) ⊗
      ((sheafCompose K (CategoryTheory.forget CommRingCat)).obj S) ⟶
        (sheafCompose K (CategoryTheory.forget CommRingCat)).obj S :=
    ⟨{ app := fun W ↦ ↾fun x ↦ @Mul.mul (S.obj.obj W) inferInstance x.1 x.2
       naturality := by intro W W' f; ext x; exact ((S.obj.map f).hom.map_mul _ _).symm }⟩
  let rOne : 𝟙_ (Sheaf K (Type (max u v w))) ⟶
      (sheafCompose K (CategoryTheory.forget CommRingCat)).obj S :=
    ⟨{ app := fun W ↦ ↾fun _ ↦ (1 : S.obj.obj W)
       naturality := by intro W W' f; ext x; exact (S.obj.map f).hom.map_one.symm }⟩
  let mAdd (M : KFlatFixedTensor.Modules S) :
      ((toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat)).obj M) ⊗
      ((toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat)).obj M) ⟶
        (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat)).obj M :=
    ⟨{ app := fun W ↦ ↾fun x ↦ @Add.add (M.val.obj W) inferInstance x.1 x.2
       naturality := by intro W W' f; ext x; exact ((M.val.map f).hom.map_add _ _).symm }⟩
  let mSMul (M : KFlatFixedTensor.Modules S) :
      ((sheafCompose K (CategoryTheory.forget CommRingCat)).obj S) ⊗
      ((toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat)).obj M) ⟶
        (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat)).obj M :=
    ⟨{ app := fun W ↦ ↾fun x ↦ @SMul.smul (S.obj.obj W) (M.val.obj W) inferInstance x.1 x.2
       naturality := by intro W W' f; ext x; exact (M.val.map_smul f x.1 x.2).symm }⟩
  have hAdd (M : KFlatFixedTensor.Modules R) := fun Z x y z hz ↦
    (pa M).binary_graph (pa M) (pa M)
      (fun V x y ↦ @Add.add (M.val.obj V) inferInstance x y)
      (mAdd ((pull a).obj M))
      (fun V x y ↦ ((pullbackPushforwardAdjunction a).unit.app M).val.app V |>.hom.map_add x y
        |>.symm)
      Z x y z hz
  have hRAdd := fun Z x y z hz ↦ pr.binary_graph pr pr
    (fun V x y ↦ @Add.add (R.obj.obj V) inferInstance x y)
    (rAdd)
    (fun V x y ↦ by rw [hr]; exact (a.hom.app V).hom.map_add x y |>.symm)
    Z x y z hz
  refine ⟨{
    ringUnderlying := pr.iso.symm
    ringAdd := ?_
    ringMul := ?_
    ringZero := ?_
    ringOne := ?_
    modules := pull a
    moduleUnderlying := em
    moduleAdd := ?_
    moduleZero := ?_
    moduleSMul := ?_
  }, rfl, rfl, HEq.rfl⟩
  · intro Z x y z hz V s
    exact congrArg (fun f ↦ f.hom.app V s) (hRAdd Z x y z hz)
  · intro Z x y z hz V s
    exact congrArg (fun f ↦ f.hom.app V s) (pr.binary_graph pr pr
      (fun V x y ↦ @Mul.mul (R.obj.obj V) inferInstance x y)
      (rMul)
      (fun V x y ↦ by rw [hr]; exact (a.hom.app V).hom.map_mul x y |>.symm)
      Z x y z hz)
  · intro Z x hx V s
    have h := congrArg (fun f ↦ f.hom.app V s) (hRAdd Z x x x (by
      intro W t
      change @Eq (R.obj.obj W) (x.hom.app W t) (_ + _)
      have hzero := hx W t
      dsimp only [id] at hzero
      rw [hzero, add_zero]))
    exact add_eq_left.mp h.symm
  · intro Z x hx V s
    exact congrArg (fun f ↦ f.hom.app V s) (pr.constant_graph
      (fun V ↦ (1 : R.obj.obj V)) (rOne)
      (fun V ↦ by rw [hr]; exact (a.hom.app V).hom.map_one.symm) Z x hx)
  · intro M Z x y z hz V s
    exact congrArg (fun f ↦ f.hom.app V s) (hAdd M Z x y z hz)
  · intro M Z x hx V s
    have h := congrArg (fun f ↦ f.hom.app V s) (hAdd M Z x x x (by
      intro W t
      change @Eq (M.val.obj W) (x.hom.app W t) (_ + _)
      have hzero := hx W t
      dsimp only [id] at hzero
      rw [hzero, add_zero]))
    exact add_eq_left.mp h.symm
  · intro M Z x y z hz V s
    exact congrArg (fun f ↦ f.hom.app V s) (pr.binary_graph (pa M) (pa M)
      (fun V x y ↦ @SMul.smul (R.obj.obj V) (M.val.obj V) inferInstance x y)
      (mSMul ((pull a).obj M))
      (fun V x y ↦ by
        rw [hr]
        exact (((pullbackPushforwardAdjunction a).unit.app M).val.app V).hom.map_smul x y
          |>.symm)
      Z x y z hz)

end SheafOfModules.SignedLineDerivedBaseChange
