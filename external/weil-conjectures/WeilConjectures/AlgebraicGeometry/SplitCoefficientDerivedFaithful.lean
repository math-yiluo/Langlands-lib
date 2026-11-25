/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

set_option linter.privateModule false
/-! # Faithfulness of scalar extension to the condensed algebraic closure

An algebraic linear projection to a finite coefficient field is continuous on every
finite-dimensional subfield and therefore acts on the condensed algebraic closure.
Tensoring its linear retraction splits the scalar-extension unit, also after localization.
-/
@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory MonObj BraidedCategory Opposite
open scoped CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false
namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F G : C ⥤ D) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
variable (H : C ⥤ D) [H.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale
variable {X : Scheme.{u}}
  (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]
  (r : S ⟶ R)
  (hlin : (φ ▷ S ≫ μ[S]) ≫ r = R ◁ r ≫ μ[R])

omit [IsMonHom φ] in
include hlin in
private lemma retract_balanced (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    (S ◁ φ ≫ μ[S]) ▷ M.X ≫ r ▷ M.X ≫ γ[R,M.X] =
      ((α_ S R M.X).hom ≫ S ◁ γ[R,M.X]) ≫ r ▷ M.X ≫ γ[R,M.X] := by
  have hr : (S ◁ φ ≫ μ[S]) ≫ r = r ▷ R ≫ μ[R] := by
    calc
      _ = (β_ S R).hom ≫ (φ ▷ S ≫ μ[S]) ≫ r := by
        simp only [Category.assoc]
        rw [← braiding_naturality_right_assoc]
        rw [reassoc_of% (IsCommMonObj.mul_comm (X := S))]
      _ = (β_ S R).hom ≫ R ◁ r ≫ μ[R] := by
        simpa only [Category.assoc] using congrArg ((β_ S R).hom ≫ ·) hlin
      _ = _ := by
        rw [← braiding_naturality_left_assoc, IsCommMonObj.mul_comm]
  rw [← comp_whiskerRight_assoc, hr, comp_whiskerRight_assoc, Mod.mul_act,
    associator_naturality_left_assoc]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc]

private noncomputable def retractOnModule (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    (Mod.comap φ).obj ((Mod.extendScalars φ).obj M) ⟶ M := by
  let f := Mod.extendDescHom φ (r ▷ M.X ≫ γ[R,M.X]) (retract_balanced R S φ r hlin M)
  refine Mod.Hom.mk' f ?_
  change (φ ▷ _ ≫ γ[S,_]) ≫ f = R ◁ f ≫ γ[R,M.X]
  apply (cancel_epi (R ◁ Mod.extendπ φ M)).1
  dsimp only [f]
  rw [Category.assoc, whisker_exchange_assoc,
    Mod.whiskerLeft_extendπ_smul_assoc, associator_inv_naturality_left_assoc]
  simp only [Mod.extendπ_extendDescHom, ← whiskerLeft_comp_assoc]
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, hlin,
    comp_whiskerRight_assoc, Mod.mul_act, associator_naturality_middle_assoc,
    Iso.inv_hom_id_assoc, whiskerLeft_comp_assoc]

private noncomputable def retractNat : Mod.extendScalars φ ⋙ Mod.comap φ ⟶ 𝟭 _ where
  app M := retractOnModule R S φ r hlin M
  naturality {M N} f := by
    apply Mod.hom_ext
    apply (cancel_epi (Mod.extendπ φ M)).1
    change Mod.extendπ φ M ≫ (Mod.extendScalarsMap φ f).hom ≫
      Mod.extendDescHom φ (r ▷ N.X ≫ γ[R,N.X]) _ =
      Mod.extendπ φ M ≫ Mod.extendDescHom φ (r ▷ M.X ≫ γ[R,M.X]) _ ≫ f.hom
    rw [Mod.extendπ_extendScalarsMap_assoc, Mod.extendπ_extendDescHom,
      Mod.extendπ_extendDescHom_assoc, whisker_exchange_assoc, Category.assoc, Mod.act_hom]

private lemma unit_retract (hret : φ ≫ r = 𝟙 R) :
    (Mod.extendRestrictAdjunction φ).unit ≫ retractNat R S φ r hlin = 𝟙 _ := by
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  change Mod.extendUnitHom φ M ≫ _ = 𝟙 M.X
  simp only [Mod.extendUnitHom, retractNat, retractOnModule, Mod.Hom.mk'_hom,
    Category.assoc, Mod.extendπ_extendDescHom]
  rw [← comp_whiskerRight_assoc]
  have he : η[S] ≫ r = η[R] := by
    rw [← IsMonHom.one_hom φ, Category.assoc, hret, Category.comp_id]
  rw [he, Mod.one_act, Iso.inv_hom_id]

end AlgebraicGeometry.ProEtale
namespace CategoryTheory
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
open scoped CategoryTheory.Obj
private lemma mapLinear (F : C ⥤ D) [F.LaxMonoidal]
    {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) (r : S ⟶ R)
    (h : (φ ▷ S ≫ μ[S]) ≫ r = R ◁ r ≫ μ[R]) :
    (F.map φ ▷ F.obj S ≫ μ[F.obj S]) ≫ F.map r =
      F.obj R ◁ F.map r ≫ μ[F.obj R] := by
  change (F.map φ ▷ F.obj S ≫ Functor.LaxMonoidal.μ F S S ≫ F.map μ[S]) ≫ F.map r =
    F.obj R ◁ F.map r ≫ Functor.LaxMonoidal.μ F R R ≫ F.map μ[R]
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc,
    Functor.LaxMonoidal.μ_natural_right_assoc, ← F.map_comp, ← F.map_comp]
  simpa only [F.map_comp, Category.assoc] using
    congrArg (Functor.LaxMonoidal.μ F R S ≫ F.map ·) h

private lemma conjugateLinear {R₀ S₀ R S : C}
    [MonObj R₀] [MonObj S₀] [MonObj R] [MonObj S]
    (a : R₀ ≅ R) (b : S₀ ≅ S) [IsMonHom a.hom] [IsMonHom b.hom]
    (φ₀ : R₀ ⟶ S₀) (φ : R ⟶ S)
    (hφ : φ ≫ b.inv = a.inv ≫ φ₀) (r₀ : S₀ ⟶ R₀)
    (h : (φ₀ ▷ S₀ ≫ μ[S₀]) ≫ r₀ = R₀ ◁ r₀ ≫ μ[R₀]) :
    (φ ▷ S ≫ μ[S]) ≫ (b.inv ≫ r₀ ≫ a.hom) =
      R ◁ (b.inv ≫ r₀ ≫ a.hom) ≫ μ[R] := by
  calc
    _ = ((φ ≫ b.inv) ⊗ₘ b.inv) ≫ μ[S₀] ≫ r₀ ≫ a.hom := by
      simp only [Category.assoc]
      rw [IsMonHom.mul_hom_assoc b.inv]
      simp only [tensorHom_def', comp_whiskerRight_assoc, Category.assoc]
      rw [← whisker_exchange_assoc]
    _ = (a.inv ⊗ₘ b.inv) ≫ (φ₀ ▷ S₀ ≫ μ[S₀]) ≫ r₀ ≫ a.hom := by
      rw [hφ]
      simp only [tensorHom_def', comp_whiskerRight_assoc, Category.assoc]
    _ = (a.inv ⊗ₘ b.inv) ≫ (R₀ ◁ r₀ ≫ μ[R₀]) ≫ a.hom := by
      simpa only [Category.assoc] using congrArg ((a.inv ⊗ₘ b.inv) ≫ · ≫ a.hom) h
    _ = _ := by
      simp only [Category.assoc]
      rw [IsMonHom.mul_hom a.hom]
      simp only [tensorHom_def', Category.assoc, ← whiskerLeft_comp_assoc]
      rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc]
      simp
end CategoryTheory

namespace Profinite
open PadicAlgCl
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
private noncomputable def fieldProjection : PadicAlgCl ℓ →ₗ[E] E :=
  (Algebra.linearMap E (PadicAlgCl ℓ)).leftInverse
private lemma fieldProjection_inclusion (x : E) :
    fieldProjection ℓ E (algebraMap E (PadicAlgCl ℓ) x) = x := by
  apply LinearMap.leftInverse_apply_of_inj
  exact LinearMap.ker_eq_bot.mpr (algebraMap E (PadicAlgCl ℓ)).injective

private noncomputable def projectSection (U : Profinite.{u})
    (f : finiteIntermediateFieldValued ℓ U) : C(U, E) :=
  ⟨fun x ↦ fieldProjection ℓ E (f.val x), by
    rcases f.property with ⟨F, hF, hvalues⟩
    let := hF
    let p := (fieldProjection ℓ E).restrictScalars ℚ_[ℓ] |>.comp F.val.toLinearMap
    exact p.continuous_of_finiteDimensional.comp (f.val.continuous.subtype_mk hvalues)⟩

private noncomputable def sectionProjection (U : Profinite.{u}) :
    finiteIntermediateFieldValued ℓ U →+ C(U, E) where
  toFun := projectSection ℓ E U
  map_zero' := by
    apply ContinuousMap.ext
    intro x
    exact map_zero (fieldProjection ℓ E)
  map_add' f g := by
    apply ContinuousMap.ext
    intro x
    exact map_add (fieldProjection ℓ E) (f.val x) (g.val x)

private noncomputable def condensedProjection : padicAlgClRingObj.{u} ℓ ⟶ continuousMapRingObj E :=
  ⟨{ app U := AddCommGrpCat.ofHom
        { toFun f := ULift.up (sectionProjection ℓ E U.unop f.down)
          map_zero' := congrArg ULift.up (map_zero (sectionProjection ℓ E U.unop))
          map_add' f g := congrArg ULift.up
            (map_add (sectionProjection ℓ E U.unop) f.down g.down) }
     naturality {U V} f := by rfl }⟩

private lemma condensedProjection_retract :
    padicSubfieldRingObjToPadicAlgCl.{u} ℓ E ≫ condensedProjection ℓ E = 𝟙 _ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  exact fieldProjection_inclusion ℓ E (f.down x)

private lemma presheafProjection_linear :
    (((padicSubfieldRingObjToPadicAlgCl.{u} ℓ E).hom ▷
        (padicAlgClRingObj ℓ).obj) ≫
      μ[padicAlgClRingPresheaf ℓ ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}]) ≫
        (condensedProjection ℓ E).hom =
      (continuousMapRingObj E).obj ◁ (condensedProjection ℓ E).hom ≫
        μ[continuousMapRingPresheaf E ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}] := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext'
  intro a b
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change fieldProjection ℓ E ((algebraMap E (PadicAlgCl ℓ)) (a.down x) * b.down.val x) =
    a.down x * fieldProjection ℓ E (b.down.val x)
  simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using
    (fieldProjection ℓ E).map_smul (a.down x) (b.down.val x)

private lemma condensedProjection_linear :
    (padicSubfieldRingObjToPadicAlgCl.{u} ℓ E ▷ padicAlgClRingObj ℓ ≫
      μ[padicAlgClRingObj ℓ]) ≫ condensedProjection ℓ E =
      continuousMapRingObj E ◁ condensedProjection ℓ E ≫ μ[continuousMapRingObj E] := by
  let J := coherentTopology Profinite.{u}
  let F := presheafToSheaf J Ab.{u + 1}
  let R := continuousMapRingPresheaf E ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}
  let S := padicAlgClRingPresheaf ℓ ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}
  let a := Sheaf.sheafifyRingPresheafIso J (continuousMapRingSheaf E)
  let b := Sheaf.sheafifyRingPresheafIso J (padicAlgClCondensedRing ℓ)
  have hφ : padicSubfieldRingObjToPadicAlgCl ℓ E ≫ b.inv =
      a.inv ≫ F.map (padicSubfieldRingObjToPadicAlgCl ℓ E).hom := by
    conv_lhs => arg 1; rw [padicSubfieldRingObjToPadicAlgCl, Sheaf.sheafCompose_map_eq]
    dsimp only [a, b, F, J]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  have hr : condensedProjection ℓ E =
      b.inv ≫ F.map (condensedProjection ℓ E).hom ≫ a.hom := by
    apply (Iso.eq_inv_comp b).mpr
    exact ((sheafificationAdjunction J Ab.{u + 1}).counit.naturality
      (condensedProjection ℓ E)).symm
  rw [hr]
  exact conjugateLinear a b _ _ hφ _
    (mapLinear F (R := R) (S := S) _ _ (presheafProjection_linear ℓ E))

end Profinite

namespace AlgebraicGeometry.ProEtale
open PadicAlgCl
end AlgebraicGeometry.ProEtale
