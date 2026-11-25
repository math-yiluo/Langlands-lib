/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.InjectiveSheafSmulEpi
public import Mathlib.Algebra.Module.Injective

/-!
# Sections of an injective sheaf of modules are injective modules

Let `Λ` be a commutative ring and `I` an injective sheaf of `Λ`-modules on a site. For every
object `U` the module of sections `I(U)` satisfies Baer's criterion
(`CategoryTheory.Sheaf.baer_obj_of_injective`), hence is an injective `Λ`-module. A linear map
`g : 𝔞 ⟶ I(U)` from an ideal `𝔞` is a morphism from the sheafified presheaf
`V ↦ 𝔞^{(Hom(V, U))}` to `I`; this presheaf is a subpresheaf of the free presheaf of
`Λ`-modules on `U`, and an extension of the morphism to the sheafified free presheaf is a
section of `I` over `U` which extends `g` to `Λ`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Opposite

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ : Type (max w v)} [CommRing Λ]

variable (Λ) in
/-- The presheaf of `Λ`-modules `V ↦ 𝔞^{(Hom(V, U))}` of finitely supported functions on the
morphisms `V ⟶ U` with values in an ideal `𝔞` of `Λ`. -/
@[simps]
noncomputable def idealFreeModuleYoneda (𝔞 : Ideal Λ) (U : C) :
    Cᵒᵖ ⥤ ModuleCat.{max w v} Λ where
  obj V := ModuleCat.of Λ ((uliftYoneda.{w}.obj U).obj V →₀ 𝔞)
  map g := ModuleCat.ofHom (Finsupp.lmapDomain 𝔞 Λ fun h ↦ ULift.up (g.unop ≫ h.down))
  map_id V := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id, Finsupp.lmapDomain_apply, LinearMap.id_coe,
      id_eq, unop_id, Category.id_comp]
    exact Finsupp.mapDomain_id
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, Finsupp.lmapDomain_apply,
      LinearMap.coe_comp, Function.comp_apply, unop_comp, Category.assoc]
    rw [← Finsupp.mapDomain_comp]
    rfl

/-- The inclusion of `V ↦ 𝔞^{(Hom(V, U))}` into the free presheaf of `Λ`-modules on `U`. -/
@[simps]
noncomputable def idealFreeModuleYonedaι (𝔞 : Ideal Λ) (U : C) :
    idealFreeModuleYoneda.{w} Λ 𝔞 U ⟶ freeModuleYoneda.{w} Λ U where
  app V := ModuleCat.ofHom (Finsupp.mapRange.linearMap 𝔞.subtype)
  naturality V W g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    exact (Finsupp.mapDomain_mapRange _ _ _ (map_zero _) (fun _ _ ↦ map_add _ _ _)).symm

/-- The inclusion of `V ↦ 𝔞^{(Hom(V, U))}` into the free presheaf is a monomorphism. -/
instance (𝔞 : Ideal Λ) (U : C) : Mono (idealFreeModuleYonedaι.{w} 𝔞 U) := by
  have (V : Cᵒᵖ) : Mono ((idealFreeModuleYonedaι.{w} 𝔞 U).app V) := by
    rw [ModuleCat.mono_iff_injective]
    exact Finsupp.mapRange_injective _ (map_zero _) Subtype.val_injective
  exact NatTrans.mono_of_mono_app _

/-- The morphism from `V ↦ 𝔞^{(Hom(V, U))}` to a presheaf `F` determined by a linear map
`𝔞 ⟶ F(U)`. -/
noncomputable def idealFreeModuleYonedaHom (𝔞 : Ideal Λ) (U : C) (F : Cᵒᵖ ⥤ ModuleCat.{max w v} Λ)
    (g : 𝔞 →ₗ[Λ] F.obj (op U)) : idealFreeModuleYoneda.{w} Λ 𝔞 U ⟶ F where
  app V := ModuleCat.ofHom (Finsupp.lsum Λ fun h ↦ (F.map h.down.op).hom ∘ₗ g)
  naturality V W k := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]
    | single a r =>
      change Finsupp.lsum Λ _ (Finsupp.mapDomain _ (Finsupp.single a r)) =
        F.map k (Finsupp.lsum Λ (fun h ↦ (F.map h.down.op).hom ∘ₗ g) (Finsupp.single a r))
      rw [Finsupp.mapDomain_single, Finsupp.lsum_single, Finsupp.lsum_single]
      change (F.map ((k.unop ≫ a.down).op)) (g r) = _
      rw [op_comp, F.map_comp]
      rfl

lemma idealFreeModuleYonedaHom_app_single (𝔞 : Ideal Λ) (U : C)
    (F : Cᵒᵖ ⥤ ModuleCat.{max w v} Λ) (g : 𝔞 →ₗ[Λ] F.obj (op U)) (a : 𝔞) :
    (idealFreeModuleYonedaHom.{w} 𝔞 U F g).app (op U) (Finsupp.single (ULift.up (𝟙 U)) a) =
      g a := by
  change Finsupp.lsum Λ _ (Finsupp.single _ a) = g a
  rw [Finsupp.lsum_single]
  simp

variable [HasSheafify J (ModuleCat.{max w v} Λ)]

/-- **Sections of an injective sheaf of modules satisfy Baer's criterion.** For an injective
sheaf `I` of `Λ`-modules and an object `U`, every linear map `𝔞 ⟶ I(U)` from an ideal of `Λ`
extends to `Λ`: it is a morphism to `I` from the sheafification of `V ↦ 𝔞^{(Hom(V, U))}`, which
extends to the sheafified free presheaf on `U` by injectivity of `I`. -/
theorem baer_obj_of_injective (I : Sheaf J (ModuleCat.{max w v} Λ)) [Injective I] (U : C) :
    Module.Baer Λ (I.obj.obj (op U)) := by
  intro 𝔞 g
  let i : (presheafToSheaf J _).obj (idealFreeModuleYoneda.{w} Λ 𝔞 U) ⟶
      (presheafToSheaf J _).obj (freeModuleYoneda.{w} Λ U) :=
    (presheafToSheaf J _).map (idealFreeModuleYonedaι.{w} 𝔞 U)
  let f : (presheafToSheaf J _).obj (idealFreeModuleYoneda.{w} Λ 𝔞 U) ⟶ I :=
    ⟨sheafifyLift J (idealFreeModuleYonedaHom.{w} 𝔞 U I.obj g) I.property⟩
  let ψ := Injective.factorThru f i
  have hψ : i ≫ ψ = f := Injective.comp_factorThru f i
  let y : I.obj.obj (op U) := ψ.hom.app (op U)
    ((toSheafify J (freeModuleYoneda.{w} Λ U)).app (op U) (freeModuleYonedaGen.{w} U))
  refine ⟨LinearMap.toSpanSingleton Λ _ y, fun x hx ↦ ?_⟩
  rw [LinearMap.toSpanSingleton_apply]
  have h₁ : x • freeModuleYonedaGen.{w} (Λ := Λ) U =
      (idealFreeModuleYonedaι.{w} 𝔞 U).app (op U) (Finsupp.single (ULift.up (𝟙 U)) ⟨x, hx⟩) := by
    change x • Finsupp.single _ (1 : Λ) =
      Finsupp.mapRange 𝔞.subtype (map_zero _) (Finsupp.single _ _)
    rw [Finsupp.mapRange_single, Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl
  have h₂ : (toSheafify J (freeModuleYoneda.{w} Λ U)).app (op U)
      ((idealFreeModuleYonedaι.{w} 𝔞 U).app (op U) (Finsupp.single (ULift.up (𝟙 U)) ⟨x, hx⟩)) =
      i.hom.app (op U) ((toSheafify J (idealFreeModuleYoneda.{w} Λ 𝔞 U)).app (op U)
        (Finsupp.single (ULift.up (𝟙 U)) ⟨x, hx⟩)) := by
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← NatTrans.comp_app,
      ← NatTrans.comp_app]
    exact congr_app (toSheafify_naturality J (idealFreeModuleYonedaι.{w} 𝔞 U)) (op U) ▸ rfl
  calc x • y
      = ψ.hom.app (op U) ((toSheafify J (freeModuleYoneda.{w} Λ U)).app (op U)
          (x • freeModuleYonedaGen.{w} U)) := by
        rw [map_smul, map_smul]
    _ = f.hom.app (op U) ((toSheafify J (idealFreeModuleYoneda.{w} Λ 𝔞 U)).app (op U)
          (Finsupp.single (ULift.up (𝟙 U)) ⟨x, hx⟩)) := by
        rw [h₁, h₂, ← hψ]
        rfl
    _ = g ⟨x, hx⟩ := by
        change ((toSheafify J _ ≫ sheafifyLift J (idealFreeModuleYonedaHom.{w} 𝔞 U I.obj g)
          I.property).app (op U)) _ = _
        rw [toSheafify_sheafifyLift]
        exact idealFreeModuleYonedaHom_app_single 𝔞 U I.obj g ⟨x, hx⟩

/-- **Sections of an injective sheaf of modules are injective modules.** -/
theorem injective_obj_of_injective (I : Sheaf J (ModuleCat.{max w v} Λ)) [Injective I] (U : C) :
    Module.Injective Λ (I.obj.obj (op U)) :=
  (baer_obj_of_injective I U).injective

end Sheaf

end CategoryTheory
