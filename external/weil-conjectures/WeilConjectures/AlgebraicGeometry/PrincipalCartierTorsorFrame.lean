/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.PrincipalCartierIdealFrame
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.InternalHomRestrictScheme
import WeilConjectures.AlgebraicGeometry.Modules.Endomorphism

/-! # The frame of a principal Cartier divisor
Source: Stacks Tags 01WQ and 0A45, the principal-chart calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
open scoped Scheme.Modules

private theorem divisor_section_eq_local {D T : Scheme.{u}} (i : D ⟶ T) :
    supportedDivisorSection i =
      (SheafOfModules.homObjUnitIso (Scheme.Modules.unit T)).inv ≫
        Scheme.Modules.dualMap i.ker.toModulesι := by
  ext U x : 3
  change @Eq
    ((PresheafOfModules.restrictOver T.sheaf.obj U).obj i.ker.toModules.val ⟶
      (PresheafOfModules.restrictOver T.sheaf.obj U).obj (Scheme.Modules.unit T).val) _ _
  ext V : 2
  ext y
  change T.presheaf.map V.unop.hom.op (show Γ(T, U) from x) *
      (show Γ(T, V.unop.left) from (i.ker.toModulesι.val.app (op V.unop.left)) y) =
    (show Γ(T, V.unop.left) from (i.ker.toModulesι.val.app (op V.unop.left)) y) *
      T.presheaf.map V.unop.hom.op x
  exact mul_comm _ _

private theorem global_divisor_frame (T : Scheme.{u}) (f : Γ(T, ⊤))
    (hI : (T.zeroLocusSubschemeι {f}).ker.IsInvertible) :
    ∃ e : Scheme.Modules.unit T ≅ (T.zeroLocusSubschemeι {f}).ker.toModulesᵛ,
      supportedDivisorSection (T.zeroLocusSubschemeι {f}) =
        Scheme.Modules.smulHom (Scheme.Modules.unit T) f ≫ e.hom := by
  obtain ⟨φ, hφ⟩ := Scheme.principalCartierIdealFrame T f hI
  let e := (SheafOfModules.homObjUnitIso (Scheme.Modules.unit T)).symm ≪≫
    (Scheme.Modules.dualFunctor T).mapIso φ.symm.op
  refine ⟨e, ?_⟩
  rw [divisor_section_eq_local]
  ext U x : 3
  change @Eq
    ((PresheafOfModules.restrictOver T.sheaf.obj U).obj
        (T.zeroLocusSubschemeι {f}).ker.toModules.val ⟶
      (PresheafOfModules.restrictOver T.sheaf.obj U).obj (Scheme.Modules.unit T).val) _ _
  ext V : 2
  ext y
  have h := hφ V.unop.left (φ.inv.app V.unop.left y)
  have hc : φ.hom.app V.unop.left (φ.inv.app V.unop.left y) = y := by
    change (φ.inv.app V.unop.left ≫ φ.hom.app V.unop.left) y = y
    rw [← Scheme.Modules.Hom.comp_app, φ.inv_hom_id, Scheme.Modules.Hom.id_app]
    rfl
  change (show Γ(T, V.unop.left) from
      (T.zeroLocusSubschemeι {f}).ker.toModulesι.app V.unop.left y) *
      T.presheaf.map V.unop.hom.op (show Γ(T, U) from x) =
    (show Γ(T, V.unop.left) from φ.inv.app V.unop.left y) *
      T.presheaf.map V.unop.hom.op
        (T.presheaf.map (homOfLE le_top).op f * (show Γ(T, U) from x))
  change (T.zeroLocusSubschemeι {f}).ker.toModulesι.app V.unop.left
      (φ.hom.app V.unop.left (φ.inv.app V.unop.left y)) = _ at h
  rw [hc] at h
  have hΓ : (show Γ(T, V.unop.left) from
      (T.zeroLocusSubschemeι {f}).ker.toModulesι.app V.unop.left y) =
    (show Γ(T, V.unop.left) from φ.inv.app V.unop.left y) *
      T.presheaf.map (homOfLE le_top).op f := h
  rw [hΓ, map_mul, Scheme.presheaf_map_map_apply]
  rw [show V.unop.hom ≫ homOfLE le_top = homOfLE le_top from Subsingleton.elim _ _]
  ring

private theorem pullback_section_eq_local {D T : Scheme.{u}} (i : D ⟶ T)
    (W : T.Opens) :
    supportedDivisorSectionPullback i W =
      (Scheme.Modules.pullback W.ι).map (supportedDivisorSection i) := by
  let e := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction W.ι)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction W.ι)
  change (e.app _).inv ≫ (Scheme.Modules.tensorPullback W.ι).map
    (supportedDivisorSection i) ≫ (e.app _).hom = _
  erw [e.hom.naturality, e.inv_hom_id_app_assoc]

/-- The dual frame of a principal Cartier ideal is global, and its complementary
canonical section is that frame acted on by the equation as a unit.
Source: Stacks Tags 01WQ and 0A45 (blueprint: lem-pur-principal-cartier-torsor-frame).
Proof: the equation is a global free generator of its invertible ideal. Dualize
its associated isomorphism to obtain a frame of the dual ideal. The dual of the
ideal inclusion is the equation times this frame, by functoriality of internal
Hom. Pull back to the basic open where the equation is a unit. Naturality of the
module pseudofunctor identifies restriction of the global frame with this pulled
frame; the torsor action is multiplication by that unit. Injectivity of the map
from torsor frames to their underlying isomorphisms gives the assertion. -/
theorem principalCartierTorsorFrame (T : Scheme.{u}) (f : Γ(T, ⊤))
    (hI : (T.zeroLocusSubschemeι {f}).ker.IsInvertible) :
    let := hI.isInvertible_dual_toModules
    let := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
      (Scheme.Modules.dual (T.zeroLocusSubschemeι {f}).ker.toModules)
    let P := Scheme.Modules.etaleIsoTorsor
      (Scheme.Modules.dual (T.zeroLocusSubschemeι {f}).ker.toModules)
    ∃ e : P.sheaf.obj.obj (op (Scheme.Etale.mk (𝟙 T))),
      ∀ τ : P.sheaf.obj.obj (op (Scheme.Etale.mk (T.basicOpen f).ι)),
        Scheme.Modules.etaleIsoTorsorVal _ τ =
          supportedDivisorSectionPullback (T.zeroLocusSubschemeι {f}) (T.basicOpen f) →
        τ = P.vadd (op (Scheme.Etale.mk (T.basicOpen f).ι))
          ⟨Additive.ofMul (T.basicOpenUnit f)⟩
          (P.sheaf.obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from
            (Scheme.Etale.mk (T.basicOpen f).ι)).op e) := by
  let := hI.isInvertible_dual_toModules
  let := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual (T.zeroLocusSubschemeι {f}).ker.toModules)
  dsimp only
  obtain ⟨e, he⟩ := global_divisor_frame T f hI
  let eg := Scheme.Modules.etaleIsoTorsorMk
    (Scheme.Modules.dual (T.zeroLocusSubschemeι {f}).ker.toModules)
    (U := op (Scheme.Etale.mk (𝟙 T)))
    ((Scheme.Modules.pullback (𝟙 T)).map e.hom) (by infer_instance)
  refine ⟨eg, ?_⟩
  intro τ hτ
  apply Scheme.Modules.etaleIsoTorsorVal_injective
    (Scheme.Modules.dual (T.zeroLocusSubschemeι {f}).ker.toModules)
  rw [hτ, Scheme.Modules.etaleIsoTorsorVal_vadd, pullback_section_eq_local,
    he, Functor.map_comp, Scheme.Modules.pullback_map_smulHom]
  change Scheme.Modules.smulHom _ ((T.basicOpen f).ι.appTop f) ≫
      (Scheme.Modules.pullback (T.basicOpen f).ι).map e.hom =
    Scheme.Modules.smulHom _ (T.basicOpenUnit f).val ≫ _
  rw [show (T.basicOpenUnit f).val = (T.basicOpen f).ι.appTop f from
    (T.isUnit_ι_appTop_basicOpen f).unit_spec]
  congr 1
  change (Scheme.Modules.pullback (T.basicOpen f).ι).map e.hom =
    (modulesPseudofunctor.presheafHom (Scheme.Modules.unitObj T)
      (Scheme.Modules.dual (T.zeroLocusSubschemeι {f}).ker.toModules)).map
      (((Scheme.toProEt T ⋙ Scheme.ProEt.forget T).map
        ((MorphismProperty.Over.mkIdTerminal @Etale T).from
          (Scheme.Etale.mk (T.basicOpen f).ι))).op)
      ((Scheme.Modules.pullback (𝟙 T)).map e.hom)
  symm
  exact Pseudofunctor.LocallyDiscreteOpToCat.pullHom_map (F := modulesPseudofunctor) e.hom (𝟙 T)
    (T.basicOpen f).ι (T.basicOpen f).ι

end AlgebraicGeometry.Etale
