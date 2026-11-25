/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all WeilConjectures.AlgebraicGeometry.TorsionControlledFormalRestriction
import all WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # The affine restriction dictionary for formal functions

Source: Stacks Project, Theorem 02OC and Lemma 088B, affine reduction.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem affine_restriction_appTop {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    (Scheme.ΓSpecIso Γ(Y, U)).inv ≫ ((f ∣_ U) ≫ hU.isoSpec.hom).appTop =
      f.app U ≫ X.presheaf.map (eqToHom (f ⁻¹ᵁ U).ι_image_top).op := by
  rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop,
    ← Category.assoc, Iso.inv_hom_id_assoc]
  rw [morphismRestrict_appTop]
  simp only [Scheme.Opens.topIso_inv]
  rw [← Category.assoc, Scheme.Hom.naturality]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2

private noncomputable def affineRestrictionSectionsIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U) :
    Scheme.Modules.pushforward f ⋙ SheafOfModules.evaluation Y.ringCatSheaf (op U) ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ⋙
        (RingedSpace.globalSectionsFunctor (f ⁻¹ᵁ U).toScheme.toRingedSpace ⋙
          ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso Γ(Y, U)).inv ≫ ((f ∣_ U) ≫ hU.isoSpec.hom).appTop).hom) := by
  let V := f ⁻¹ᵁ U
  refine NatIso.ofComponents (fun M ↦ ModuleCat.isoMk
    (M.presheaf.mapIso (eqToIso V.ι_image_top).op) ?_) ?_
  · intro r
    change M.presheaf.map (eqToHom V.ι_image_top).op ≫
      ((M.restrict V.ι).smul
        (((Scheme.ΓSpecIso Γ(Y, U)).inv ≫ ((f ∣_ U) ≫ hU.isoSpec.hom).appTop).hom r)).asHom =
      (M.smul ((f.app U).hom r)).asHom ≫ M.presheaf.map (eqToHom V.ι_image_top).op
    rw [affine_restriction_appTop]
    have hr := Scheme.Modules.smul_restrictAppIso_hom V.ι M ⊤
      ((f.app U ≫ X.presheaf.map (eqToHom V.ι_image_top).op).hom r)
    simp only [Scheme.Modules.restrictAppIso, Iso.refl_hom, Category.comp_id,
      Category.id_comp, Scheme.Opens.ι_appIso, Iso.refl_inv] at hr
    erw [hr]
    exact (M.map_comp_smul (eqToHom V.ι_image_top) ((f.app U).hom r)).symm
  · intro M N t
    apply (Functor.map_injective (forget₂ (ModuleCat Γ(Y, U)) Ab))
    change t.app V ≫ N.presheaf.map (eqToHom V.ι_image_top).op =
      M.presheaf.map (eqToHom V.ι_image_top).op ≫ t.app (V.ι ''ᵁ ⊤)
    exact (t.mapPresheaf.naturality _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The affine chart identifies the original sections and quotient system with the
sections and quotient system of the restricted proper morphism to a spectrum.
This is a finite-level dictionary; it asserts no completion or limit isomorphism.
Source: Stacks Project, Theorem 02OC and Lemma 088B; Schemes, Tags 01I8 and 01IC.
(blueprint: lem-weil-pbc-formal-functions-affine-restriction-dictionary)

Proof: Let V = f^(-1)U and g = (f restricted to U) followed by U = Spec Gamma(Y,U).
The restriction square is cartesian, so properness of f gives properness of g.
Restriction to V preserves coherence of F. The affine ideal correspondence identifies
J restricted to U with the ideal sheaf associated with J(U). Functoriality of comap,
and the restriction square, then give the displayed equality of ideals on V.
Pushforward sections over U are F sections over V. Global sections of F restricted to
V are the same sections via the restriction top isomorphism. The affine chart formula
for g.appTop identifies their scalar action with the original Gamma(Y,U)-action;
this gives a. Restriction preserves ideal products and powers and preserves cokernels.
The cokernel comparisons give the level maps b_n from the restricted quotient sections
to the original quotient sections. Their composites with quotient projections are the
restriction of those original projections, so these maps give the displayed equation.
Cancel the quotient epimorphisms to check every transition square, giving b as a natural
isomorphism. These steps use only restriction and finite-level quotients; they do not
use the theorem on formal functions. Empty U, F=0, and zero or unit J satisfy the same
restriction and cokernel universal properties.
-/
theorem formalFunctions_affine_restriction_dictionary
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f] (F : CoherentModules X)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    let R := Γ(Y, U)
    let I := J.ideal ⟨U, hU⟩
    let V := f ⁻¹ᵁ U
    let Z := V.toScheme
    let g := (f ∣_ U) ≫ hU.isoSpec.hom
    let K := (J.comap f).comap V.ι
    let P := (Scheme.Modules.restrictFunctor V.ι).obj F.obj
    let G := RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
      ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom
    let H := (Scheme.Modules.pushforward f).obj F.obj
    let T := formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f
    let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
    IsProper g ∧ RingedSpace.IsCoherent Z.toRingedSpace P ∧
      K = (Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso R).inv.hom)).comap g ∧
      ∃ a : E.obj H ≅ G.obj P,
        ∃ b : formalCompletionSystem K P ⋙ G ≅ T ⋙ E,
          ∀ n : ℕ, a.hom ≫ G.map (formalModuleQuotientπ K (n + 1) P) ≫
            b.hom.app (op n) = E.map ((Scheme.Modules.pushforward f).map
              (formalModuleQuotientπ (J.comap f) (n + 1) F.obj)) := by
  dsimp only
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hproper : IsProper ((f ∣_ U) ≫ hU.isoSpec.hom) := inferInstance
  have hcoh : RingedSpace.IsCoherent (f ⁻¹ᵁ U).toScheme.toRingedSpace
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F.obj) := by
    have hF := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
      X F.obj).mp F.property
    have : F.obj.IsQuasicoherent := hF.1
    have : F.obj.IsFiniteType := hF.2
    exact (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mpr
      ⟨inferInstance, Scheme.Modules.finiteType_restrict _ _⟩
  have hideal : (J.comap f).comap (f ⁻¹ᵁ U).ι =
      (Scheme.IdealSheafData.ofIdealTop
        ((J.ideal ⟨U, hU⟩).map (Scheme.ΓSpecIso Γ(Y, U)).inv.hom)).comap
        ((f ∣_ U) ≫ hU.isoSpec.hom) := by
    let Q := Scheme.IdealSheafData.ofIdealTop
      ((J.ideal ⟨U, hU⟩).map (Scheme.ΓSpecIso Γ(Y, U)).inv.hom)
    have hc : J.comap U.ι = Q.comap hU.isoSpec.hom := by
      let : IsAffine U.toScheme := hU
      apply Scheme.IdealSheafData.ext_of_isAffine
      rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
        Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
      simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
      change (J.ideal ⟨U.ι ''ᵁ ⊤, _⟩).comap (RingHom.id Γ(Y, U.ι ''ᵁ ⊤)) =
        (Q.ideal ⟨hU.isoSpec.hom ''ᵁ ⊤, _⟩).comap
          (hU.isoSpec.hom.appIso ⊤).inv.hom
      simp only [Ideal.comap_id]
      have hu : U.ι ''ᵁ ⊤ = U := U.ι_image_top
      change _ = (Q.ideal ⟨hU.isoSpec.hom ''ᵁ ⊤, _⟩).comap
        (hU.isoSpec.hom.appIso ⊤).commRingCatIsoToRingEquiv.symm.toRingHom
      erw [← Ideal.map_comap_of_equiv
        (hU.isoSpec.hom.appIso ⊤).commRingCatIsoToRingEquiv]
      simp only [Q, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map,
        ← CommRingCat.hom_comp]
      change J.ideal ⟨U.ι ''ᵁ ⊤, _⟩ = (J.ideal ⟨U, hU⟩).map
        ((Scheme.ΓSpecIso Γ(Y, U)).inv ≫
          (Spec Γ(Y, U)).presheaf.map (homOfLE le_top).op ≫
          (hU.isoSpec.hom.appIso ⊤).hom).hom
      rw [Scheme.Hom.appIso_hom]
      rw [Scheme.Hom.naturality_assoc]
      rw [show hU.isoSpec.hom.app ⊤ = hU.isoSpec.hom.appTop from rfl,
        IsAffineOpen.isoSpec_hom_appTop]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Scheme.Opens.topIso_inv,
        Scheme.Opens.toScheme_presheaf_map, ← Functor.map_comp]
      convert (J.map_ideal
        (U := ⟨U.ι ''ᵁ ⊤, (isAffineOpen_top U.toScheme).image_of_isOpenImmersion U.ι⟩)
        (V := ⟨U, hU⟩) hu.le).symm using 1
      congr 3
    change (J.comap f).comap (f ⁻¹ᵁ U).ι = Q.comap _
    rw [← Scheme.IdealSheafData.comap_comp,
      ← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp, hc,
      ← Scheme.IdealSheafData.comap_comp]
  refine ⟨hproper, hcoh, hideal, ?_⟩
  have hF := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X F.obj).mp F.property
  have : F.obj.IsQuasicoherent := hF.1
  let V := f ⁻¹ᵁ U
  let R := Scheme.Modules.restrictFunctor V.ι
  let G := RingedSpace.globalSectionsFunctor V.toScheme.toRingedSpace ⋙
    ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso Γ(Y, U)).inv ≫ ((f ∣_ U) ≫ hU.isoSpec.hom).appTop).hom
  let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
  let S := formalCompletionSystem (J.comap f) F.obj
  let e := affineRestrictionSectionsIso f U hU
  let c := restrictionCompletionIso (J.comap f) F.obj V
  let b := Functor.isoWhiskerRight c G ≪≫ Functor.associator S R G ≪≫
    Functor.isoWhiskerLeft S e.symm ≪≫
    (Functor.associator S (Scheme.Modules.pushforward f) E).symm
  refine ⟨e.app F.obj, b, ?_⟩
  intro n
  change e.hom.app F.obj ≫ G.map (formalModuleQuotientπ ((J.comap f).comap V.ι)
      (n + 1) (R.obj F.obj)) ≫
      G.map (restrictionQuotientIso (J.comap f) F.obj V (n + 1)).hom ≫
      e.inv.app (formalModuleQuotient (J.comap f) (n + 1) F.obj) = _
  rw [← Category.assoc (G.map _) (G.map _) (e.inv.app _),
    ← G.map_comp, restrictionQuotientIso_π]
  rw [← Category.assoc]
  erw [← e.hom.naturality]
  simp

end AlgebraicGeometry
