/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde

/-!
# The sheaf associated with an affine quotient

The affine quotient presentation identifies the associated quotient module sheaf
with the restricted pushforward of the closed subscheme's structure sheaf.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme.Modules in
private theorem restrict_iso_pushforward {X Y : Scheme.{u}} (e : X ≅ Y)
    (M : Y.Modules) :
    Nonempty (M.restrict e.hom ≅ (pushforward e.inv).obj M) := by
  let a : (pushforward e.inv ⋙ pushforward e.hom).obj M ≅ M :=
    (pushforwardComp e.inv e.hom).app M ≪≫
      (pushforwardCongr e.inv_hom_id).app M ≪≫ (pushforwardId Y).app M
  exact ⟨(restrictFunctor e.hom).mapIso a.symm ≪≫
    (restrictFunctorAdjCounitIso e.hom).app ((pushforward e.inv).obj M)⟩

open Scheme.Modules in
private theorem spectrum_pushforward_unit_iso {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    Nonempty (tilde ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S)) ≅
      (pushforward (Spec.map φ)).obj (SheafOfModules.unit (Spec S).ringCatSheaf)) := by
  let M := SheafOfModules.unit (Spec S).ringCatSheaf
  have : IsIso ((pushforward (Spec.map φ)).obj M).fromTildeΓ :=
    isIso_fromTildeΓ_pushforward φ M
  let a := (pushforwardSpecMapCompΓIso φ).app M ≪≫
    (ModuleCat.restrictScalars φ.hom).mapIso (tilde.isoTop (ModuleCat.of S S)).symm
  exact ⟨(tilde.functor R).mapIso a.symm ≪≫
    asIso ((pushforward (Spec.map φ)).obj M).fromTildeΓ⟩

/-- Basic-open calculation identifies the associated quotient sheaf with the restricted
pushforward of the closed subscheme structure sheaf.
Source: Stacks Project, Lemma 26.7.3(2), Tag 01I9, with the affine chart
and quotient presentation of Tag 068C.
(blueprint: lem-sc-affine-quotient-restricted-iso).

Proof: Write A = Γ(Y,U). Under the affine chart hU.isoSpec and the given
presentation e, the compatibility he identifies the restricted immersion with
Spec(A/I) → Spec A. For every basic open D(g) in Spec A, its inverse image is
D(g mod I). Sections of the pushforward structure sheaf on D(g) are therefore
(A/I)[1/g], as a module over A[1/g]. The associated sheaf of the A-module A/I
has exactly these sections, with the same localized A-action. These identifications
commute with restrictions between basic opens because both restrictions are the
canonical localization maps. Basic opens form a basis stable under intersection,
so the identifications glue uniquely to an isomorphism of module sheaves on Spec A.
Transport this isomorphism along hU.isoSpec to obtain the asserted isomorphism on U.
The argument also covers I = ⊤ (both sheaves are zero), I = ⊥, and empty U. -/
theorem affine_quotient_restricted_iso {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (U : Y.Opens) (hU : IsAffineOpen U) (I : Ideal (Γ(Y, U)))
    (e : Scheme.Opens.toScheme (i ⁻¹ᵁ U) ≅
      Spec (CommRingCat.of ((Γ(Y, U) : Type u) ⧸ I)))
    (he : i ∣_ U ≫ U.toSpecΓ =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    Nonempty (((tilde.functor Γ(Y, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).obj
        (ModuleCat.of (Γ(Y, U) : Type u) ((Γ(Y, U) : Type u) ⧸ I))) ≅
      ((Scheme.Modules.restrictFunctor U.ι).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))) := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let O := SheafOfModules.unit Z.ringCatSheaf
  obtain ⟨a⟩ := spectrum_pushforward_unit_iso
    (CommRingCat.ofHom (Ideal.Quotient.mk I))
  obtain ⟨b⟩ := restrict_iso_pushforward hU.isoSpec ((Scheme.Modules.pushforward q).obj
    (SheafOfModules.unit
      (Spec (CommRingCat.of ((Γ(Y, U) : Type u) ⧸ I))).ringCatSheaf))
  obtain ⟨c⟩ := by
    let r : U.ι.opensFunctor ⋙ TopologicalSpace.Opens.map i.base ≅
        TopologicalSpace.Opens.map (i ∣_ U).base ⋙ (i ⁻¹ᵁ U).ι.opensFunctor :=
      NatIso.ofComponents (fun V ↦ eqToIso (image_morphismRestrict_preimage i U V).symm)
    change Nonempty (((SheafOfModules.pushforward i.toRingCatSheafHom) ⋙
      Scheme.Modules.restrictFunctor U.ι).obj O ≅
      (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ U).ι ⋙
        Scheme.Modules.pushforward (i ∣_ U)).obj O)
    unfold Scheme.Modules.restrictFunctor Scheme.Modules.pushforward
    refine ⟨((SheafOfModules.pushforwardComp _ _) ≪≫ ?_ ≪≫
      (SheafOfModules.pushforwardComp _ _).symm).app O⟩
    refine SheafOfModules.pushforwardCongr₂ _ r.symm ?_
    ext V x
    change Z.presheaf.map (eqToHom (image_morphismRestrict_preimage i U V.unop)).op
        (i.app (U.ι ''ᵁ V.unop) ((U.ι.appIso V.unop).inv x)) =
      ((i ⁻¹ᵁ U).ι.appIso ((i ∣_ U) ⁻¹ᵁ V.unop)).inv ((i ∣_ U).app V.unop x)
    rw [Scheme.Opens.ι_appIso, Scheme.Opens.ι_appIso]
    simp only [Iso.refl_inv]
    exact (ConcreteCategory.congr_hom (morphismRestrict_app i U V.unop) x).symm
  obtain ⟨d⟩ := restrict_iso_pushforward e.symm
    (SheafOfModules.unit (i ⁻¹ᵁ U).toScheme.ringCatSheaf)
  have hi : e.hom ≫ q ≫ hU.isoSpec.inv = i ∣_ U := by
    change (e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫
      hU.isoSpec.inv = i ∣_ U
    rw [← he, Category.assoc, hU.toSpecΓ_isoSpec_inv, Category.comp_id]
  let eunit := d.symm ≪≫ Scheme.Modules.restrictUnitIso e.inv
  exact ⟨(Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapIso a ≪≫ b ≪≫
    (Scheme.Modules.pushforwardComp q hU.isoSpec.inv).app _ ≪≫
    (Scheme.Modules.pushforward (q ≫ hU.isoSpec.inv)).mapIso eunit.symm ≪≫
    (Scheme.Modules.pushforwardComp e.hom (q ≫ hU.isoSpec.inv)).app _ ≪≫
    (Scheme.Modules.pushforwardCongr hi).app _ ≪≫
    (Scheme.Modules.pushforward (i ∣_ U)).mapIso
      (Scheme.Modules.restrictUnitIso (i ⁻¹ᵁ U).ι).symm ≪≫ c.symm⟩

end AlgebraicGeometry
