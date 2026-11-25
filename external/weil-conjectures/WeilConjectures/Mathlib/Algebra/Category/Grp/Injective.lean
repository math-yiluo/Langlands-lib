/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Injective abelian groups and presheaves under universe lifts

The universe lift `AddCommGrpCat.uliftFunctor : AddCommGrpCat.{v} ⥤ AddCommGrpCat.{max v w}`
has no left adjoint, but it still preserves injective objects: an injective abelian group is
divisible, and so is its universe lift. For an essentially small category `C`, the same holds
for presheaves of abelian groups on `C`: an injective presheaf `P` is a retract of a product
`∏ₛ Rₛ(Jₛ)` of the right adjoints of the evaluations at the objects of a small model of `C`
applied to injective abelian groups `Jₛ`, and lifting universes commutes with these.

## Main statements

- `AddCommGrpCat.injective_uliftFunctor_obj`: the universe lift of an injective abelian group is
  injective.
- `CategoryTheory.Presheaf.injective_comp_uliftFunctor`: the universe lift of an injective
  presheaf of abelian groups on an essentially small category is injective.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace AddCommGrpCat

/-- An injective abelian group is divisible. -/
lemma exists_zsmul_eq_of_injective (A : AddCommGrpCat.{v}) [Injective A] (a : A) {n : ℤ}
    (hn : n ≠ 0) : ∃ b : A, n • b = a := by
  let f : AddCommGrpCat.of (ULift.{v} ℤ) ⟶ AddCommGrpCat.of (ULift.{v} ℤ) :=
    AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun x ↦ ULift.up (n * x.down))
      (fun x y ↦ ULift.ext (by simp [mul_add])))
  have : Mono f := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro x y h
    have h' : n * x.down = n * y.down := congrArg ULift.down h
    exact ULift.ext (mul_left_cancel₀ hn h')
  let g : AddCommGrpCat.of (ULift.{v} ℤ) ⟶ A :=
    AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun x ↦ x.down • a) (fun x y ↦ by simp [add_smul]))
  refine ⟨Injective.factorThru g f (ULift.up 1), ?_⟩
  have h := ConcreteCategory.congr_hom (Injective.comp_factorThru g f) (ULift.up 1)
  have e : f (ULift.up 1) = n • ULift.up 1 := ULift.ext (by simp [f])
  have e' : g (ULift.up 1) = a := by simp [g]
  rw [ConcreteCategory.comp_apply, e, map_zsmul, e'] at h
  exact h

/-- The universe lift of an injective abelian group is divisible. -/
@[instance_reducible]
noncomputable def divisibleByULiftOfInjective (A : AddCommGrpCat.{v}) [Injective A] :
    DivisibleBy (ULift.{w} A) ℤ := by
  classical exact
  { div a n := if hn : n = 0 then 0 else
      ULift.up (exists_zsmul_eq_of_injective A a.down hn).choose
    div_zero a := dite_eq_left rfl
    div_cancel {n} a hn := by
      rw [dite_eq_right hn]
      exact ULift.ext (exists_zsmul_eq_of_injective A a.down hn).choose_spec }

/-- The universe lift of an injective abelian group is injective. -/
instance injective_uliftFunctor_obj (A : AddCommGrpCat.{v}) [Injective A] :
    Injective (uliftFunctor.{w}.obj A) := by
  let := divisibleByULiftOfInjective.{w} A
  exact injective_of_divisible (ULift.{w} A)

end AddCommGrpCat

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]

/-- Lifting universes commutes with the right adjoint of the evaluation at an object. -/
noncomputable def evaluationRightAdjointULiftIso (c : Cᵒᵖ) (A : AddCommGrpCat.{v}) :
    (evaluationRightAdjoint AddCommGrpCat.{v} c).obj A ⋙ AddCommGrpCat.uliftFunctor.{w} ≅
      (evaluationRightAdjoint AddCommGrpCat.{max v w} c).obj
        (AddCommGrpCat.uliftFunctor.{w}.obj A) :=
  NatIso.ofComponents (fun t ↦ PreservesProduct.iso AddCommGrpCat.uliftFunctor.{w} _)
    (fun {t t'} f ↦ by
      refine Pi.hom_ext _ _ fun g ↦ ?_
      simp only [Functor.comp_obj, Functor.comp_map,
        evaluationRightAdjoint_obj_map, PreservesProduct.iso_hom, Category.assoc,
        limit.lift_π, Fan.mk_pt, Fan.mk_π_app, piComparison_comp_π]
      rw [← Functor.map_comp, limit.lift_π]
      rfl)

lemma injective_evaluationRightAdjoint_obj (c : Cᵒᵖ) (A : AddCommGrpCat.{v}) [Injective A] :
    Injective ((evaluationRightAdjoint AddCommGrpCat.{v} c).obj A) :=
  (evaluationAdjunctionLeft AddCommGrpCat.{v} c).map_injective A ‹_›

/-- **Injective presheaves after lifting universes.** If `C` is essentially small, the universe
lift of an injective presheaf of abelian groups on `C` is an injective presheaf. -/
theorem injective_comp_uliftFunctor [EssentiallySmall.{v} C] (P : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    [Injective P] : Injective (P ⋙ AddCommGrpCat.uliftFunctor.{w}) := by
  let e := equivSmallModel.{v} C
  let c (s : SmallModel.{v} C) : Cᵒᵖ := op (e.inverse.obj s)
  let R (s : SmallModel.{v} C) := evaluationRightAdjoint AddCommGrpCat.{v} (c s)
  let adj (s : SmallModel.{v} C) := evaluationAdjunctionLeft AddCommGrpCat.{v} (c s)
  let J (s : SmallModel.{v} C) := Injective.under (P.obj (c s))
  let Q := ∏ᶜ fun s ↦ (R s).obj (J s)
  let φ : P ⟶ Q := Pi.lift fun s ↦ (adj s).homEquiv _ _ (Injective.ι (P.obj (c s)))
  have hφ : Mono φ := by
    rw [NatTrans.mono_iff_mono_app']
    intro T
    let s₀ := e.functor.obj T.unop
    let g : T ⟶ c s₀ := (e.unitIso.app T.unop).inv.op
    have : IsIso g := by dsimp [g]; infer_instance
    have h : φ.app T ≫ (Pi.π (fun s ↦ (R s).obj (J s)) s₀).app T ≫ Pi.π _ g =
        P.map g ≫ Injective.ι (P.obj (c s₀)) := by
      rw [← Category.assoc, ← NatTrans.comp_app, Pi.lift_comp_π, Adjunction.homEquiv_unit]
      simp [R, adj]
    have : Mono (φ.app T ≫ (Pi.π (fun s ↦ (R s).obj (J s)) s₀).app T ≫ Pi.π _ g) := by
      rw [h]
      infer_instance
    exact mono_of_mono _ ((Pi.π (fun s ↦ (R s).obj (J s)) s₀).app T ≫ Pi.π _ g)
  let r : Q ⟶ P := Injective.factorThru (𝟙 P) φ
  have hr : φ ≫ r = 𝟙 P := Injective.comp_factorThru _ _
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.uliftFunctor.{w}
  have hQ : Injective (W.obj Q) := by
    have (s : SmallModel.{v} C) : Injective (W.obj ((R s).obj (J s))) := by
      have : Injective (J s) := Injective.injective_under _
      refine Injective.of_iso (evaluationRightAdjointULiftIso (c s) (J s)).symm ?_
      exact (evaluationAdjunctionLeft AddCommGrpCat.{max v w} (c s)).map_injective _
        inferInstance
    exact Injective.of_iso (PreservesProduct.iso W _).symm inferInstance
  refine ⟨fun {A B} a f _ ↦ ⟨Injective.factorThru (a ≫ W.map φ) f ≫ W.map r, ?_⟩⟩
  rw [← Category.assoc, Injective.comp_factorThru, Category.assoc, ← W.map_comp, hr,
    W.map_id]
  exact Category.comp_id _

end CategoryTheory.Presheaf
