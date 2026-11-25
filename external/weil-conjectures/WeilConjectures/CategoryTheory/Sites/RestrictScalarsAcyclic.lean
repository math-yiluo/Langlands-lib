/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.HomSheafAcyclic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars

/-!
# Restriction of scalars of injective sheaves is acyclic

Let `φ : Λ →+* Λ'` be a morphism of commutative rings and `J` a Grothendieck topology. The
restriction of scalars `res J` of an injective sheaf `I` of `Λ'`-modules is in general not an
injective sheaf of `Λ`-modules, but it is acyclic for every left exact functor `Φ` on sheaves of
`Λ`-modules which sends the morphisms that are surjective on sections to epimorphisms
(`CategoryTheory.Sheaf.rightAcyclic_restrictScalars_obj_of_injective`), e.g. for direct images.

Indeed, embedding `res I` into an injective sheaf `E` of `Λ`-modules, the adjoint morphism
`I ⟶ Hom_Λ(Λ', E)` is a split monomorphism, so `res I` is a direct summand of
`res Hom_Λ(Λ', E)`, which is the sheaf `Hom_Λ(Λ', E)` of homomorphisms out of the `Λ`-module
`Λ'` (`CategoryTheory.Sheaf.restrictScalarsCoextendScalarsObjIso`), and this sheaf is
`Φ`-acyclic (`CategoryTheory.Sheaf.rightAcyclic_homSheaf_obj`).

This is the input for the commutation of derived direct images with restriction of scalars, on
any site.
-/

@[expose] public section

universe t w v

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

section

variable {Λ Λ' : Type t} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

/-- The coextension of scalars of a `Λ`-module `N` along `φ : Λ →+* Λ'`, viewed again as a
`Λ`-module, is the module `Hom_Λ(Λ', N)` of homomorphisms out of the `Λ`-module `Λ'`. -/
noncomputable def coextendScalarsCompRestrictScalarsIso :
    ModuleCat.coextendScalars.{t, t, t} φ ⋙
        ModuleCat.restrictScalars.{t} φ ≅
      homFunctor Λ ((ModuleCat.restrictScalars.{t} φ).obj (ModuleCat.of Λ' Λ')) :=
  NatIso.ofComponents (fun N ↦ LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.restrictScalars.{t} φ).obj ((ModuleCat.coextendScalars φ).obj N))
    { toFun := fun g ↦ ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars.{t} φ).obj (ModuleCat.of Λ' Λ')) (Y := N) g
      invFun := fun g ↦ g.hom
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r g ↦ by
        refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
        let g' : (ModuleCat.restrictScalars.{t} φ).obj (ModuleCat.of Λ' Λ') →ₗ[Λ] N := g
        exact (congrArg g' (@mul_comm Λ' _ s (φ r))).trans (map_smul g' r s)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }) (fun _ ↦ rfl)

end

variable {Λ Λ' : Type (max w v)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

variable {C : Type (max w v)} [Category.{v} C] (J : GrothendieckTopology C)

/-- The restriction of scalars of the coextension `Hom_Λ(Λ', E)` of a sheaf `E` of
`Λ`-modules is the sheaf `Hom_Λ(Λ', E)` of homomorphisms out of the `Λ`-module `Λ'`. -/
noncomputable def restrictScalarsCoextendScalarsObjIso (E : Sheaf J (ModuleCat.{max w v} Λ)) :
    (restrictScalars.{max w v, v, max w v} J φ).obj
        ((sheafCompose J (ModuleCat.coextendScalars.{max w v, max w v, max w v} φ)).obj E) ≅
      (homSheaf.{max w v, v, max w v} J
        ((ModuleCat.restrictScalars.{max w v} φ).obj (ModuleCat.of Λ' Λ'))).obj E where
  hom := (sheafCompose_map _ (coextendScalarsCompRestrictScalarsIso.{max w v} φ).hom).app E
  inv := (sheafCompose_map _ (coextendScalarsCompRestrictScalarsIso.{max w v} φ).inv).app E
  hom_inv_id := by
    ext U : 3
    exact congr_app (coextendScalarsCompRestrictScalarsIso.{max w v} φ).hom_inv_id _
  inv_hom_id := by
    ext U : 3
    exact congr_app (coextendScalarsCompRestrictScalarsIso.{max w v} φ).inv_hom_id _

/-- Restriction of scalars of sheaves is faithful: it is computed sectionwise. -/
instance : (restrictScalars.{max w v, v, max w v} J φ).Faithful where
  map_injective {A B} a b h := by
    ext U : 3
    exact (ModuleCat.restrictScalars.{max w v} φ).map_injective
      (congr_app (congrArg (fun a ↦ a.hom) h) U)

variable [HasSheafify J (ModuleCat.{max w v} Λ)] [HasSheafify J (ModuleCat.{max w v} Λ')]
  [HasInjectiveResolutions (Sheaf J (ModuleCat.{max w v} Λ))]
  [EnoughInjectives (Sheaf J (ModuleCat.{max w v} Λ))]

/-- **Restriction of scalars of an injective sheaf is acyclic.** Let `Φ` be a left exact functor
on sheaves of `Λ`-modules which sends morphisms that are surjective on sections to epimorphisms.
For an injective sheaf `I` of `Λ'`-modules, the sheaf of `Λ`-modules `res I` is `Φ`-acyclic: it is
a direct summand of `res Hom_Λ(Λ', E) = Hom_Λ(Λ', E)` for an injective sheaf `E` of
`Λ`-modules containing `res I`, and the latter is `Φ`-acyclic
(`CategoryTheory.Sheaf.rightAcyclic_homSheaf_obj`). -/
theorem rightAcyclic_restrictScalars_obj_of_injective
    {D : Type*} [Category* D] [Abelian D] (Φ : Sheaf J (ModuleCat.{max w v} Λ) ⥤ D) [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hΦ : ∀ {A B : Sheaf J (ModuleCat.{max w v} Λ)} (p : A ⟶ B),
      (∀ U, Function.Surjective (p.hom.app U)) → Epi (Φ.map p))
    (I : Sheaf J (ModuleCat.{max w v} Λ')) [Injective I] :
    Φ.rightAcyclic ((restrictScalars.{max w v, v, max w v} J φ).obj I) := by
  let res := restrictScalars.{max w v, v, max w v} J φ
  let adj := restrictCoextendScalarsAdj J φ
  let E := Injective.under (res.obj I)
  -- `I` is a direct summand of `Hom_Λ(Λ', E)`
  let j : I ⟶ (sheafCompose J (ModuleCat.coextendScalars φ)).obj E :=
    adj.homEquiv _ _ (Injective.ι (res.obj I))
  have h : res.map j ≫ adj.counit.app E = Injective.ι (res.obj I) :=
    (adj.homEquiv_counit (g := j)).symm.trans ((adj.homEquiv _ _).symm_apply_apply _)
  have : Mono (res.map j) := mono_of_mono_fac h
  have : Mono j := res.mono_of_mono_map this
  let r : (sheafCompose J (ModuleCat.coextendScalars φ)).obj E ⟶ I := Injective.factorThru (𝟙 I) j
  have hjr : res.map j ≫ res.map r = 𝟙 _ := by
    rw [← res.map_comp, Injective.comp_factorThru, res.map_id]
  have hE : Φ.rightAcyclic (res.obj ((sheafCompose J (ModuleCat.coextendScalars φ)).obj E)) :=
    Φ.rightAcyclic.prop_of_iso (restrictScalarsCoextendScalarsObjIso.{w, v} φ J E).symm
      (rightAcyclic_homSheaf_obj Φ hΦ E (fun U ↦ baer_obj_of_injective.{w} E U.unop) _)
  intro q
  rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id, ← hjr,
    CategoryTheory.Functor.map_comp,
    (hE q).eq_of_tgt ((Φ.rightDerived (q + 1)).map (res.map j)) 0, Limits.zero_comp]

end CategoryTheory.Sheaf
