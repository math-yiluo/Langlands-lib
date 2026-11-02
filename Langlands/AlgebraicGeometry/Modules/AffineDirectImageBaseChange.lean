import Langlands.AlgebraicGeometry.Modules.DerivedRestriction
import Langlands.AlgebraicGeometry.Modules.SectionsBaseChangeComposition
import Langlands.AlgebraicGeometry.Modules.AffinePullbackQuasicoherent

/-! # The affine sheaf comparison and scalar sections base change -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Scheme.Modules

variable {X X' : Scheme.{u}} {R T : CommRingCat.{u}}
  (φ : R ⟶ T) (f : X ⟶ Spec R) (f' : X' ⟶ Spec T)
  (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)

/-- The actual scalar sections comparison followed by the tilde counit of the target. -/
def affineDirectImageTildeMap (M : X.Modules) :
    tilde ((ModuleCat.extendScalars φ.hom).obj ((relativeGlobalSections f).obj M)) ⟶
      (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g).obj M) :=
  tilde.map (scalarSectionsBaseChangeMap φ f f' g w M) ≫
    ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g).obj M)).fromTildeΓ

/-- On top sections the pushforward square comparison is the identity. -/
lemma pushforwardSquareIso_hom_app_top (N : X'.Modules)
    (m : Γ(N, ⊤)) :
    ((pushforwardSquareIso (Spec.map φ) f f' g w).hom.app N).app ⊤ m = m := by
  simp only [pushforwardSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Category.id_comp,
    Category.comp_id, Scheme.Modules.pushforwardCongr_hom_app_app]
  have h : (eqToHom (w ▸ rfl) : (f' ≫ Spec.map φ) ⁻¹ᵁ ⊤ ⟶ (g ≫ f) ⁻¹ᵁ ⊤) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [h, op_id]
  change N.presheaf.map (𝟙 (op ⊤)) m = m
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The adjoint of the actual sheaf comparison has the prescribed ordinary sections map. -/
lemma pushforwardBaseChange_adjoint_app_top (M : X.Modules)
    (m : (relativeGlobalSections f).obj M) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _
      (pushforwardBaseChange (Spec.map φ) f f' g w M)).app ⊤ m =
      sectionsBaseChangeMap φ f f' g w M m := by
  simp only [pushforwardBaseChange, Equiv.apply_symm_apply,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    ConcreteCategory.comp_apply, sectionsBaseChangeMap_apply]
  exact pushforwardSquareIso_hom_app_top φ f f' g w _ _

/-- The affine sheaf map agrees with the scalar comparison on the canonical global generators. -/
@[reassoc]
theorem pullback_fromTildeΓ_comp_pushforwardBaseChange (M : X.Modules) :
    (Scheme.Modules.pullback (Spec.map φ)).map
        ((Scheme.Modules.pushforward f).obj M).fromTildeΓ ≫
      pushforwardBaseChange (Spec.map φ) f f' g w M =
    (tildePullbackIso φ ((relativeGlobalSections f).obj M)).hom ≫
      affineDirectImageTildeMap φ f f' g w M := by
  dsimp only [relativeGlobalSections, Functor.comp_obj]
  apply tildePullback_hom_ext
  intro m
  rw [tildePullbackAdjoint, Adjunction.homEquiv_naturality_left,
    tildePullbackAdjoint, Adjunction.homEquiv_naturality_right]
  change ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _
      (pushforwardBaseChange (Spec.map φ) f f' g w M)).app ⊤
        (((Scheme.Modules.pushforward f).obj M).fromTildeΓ.app ⊤
          (tilde.toOpen ((moduleSpecΓFunctor (R := R)).obj
            ((Scheme.Modules.pushforward f).obj M)) ⊤ m)) =
    (affineDirectImageTildeMap φ f f' g w M).app ⊤
      ((tildePullbackAdjoint φ
        (tildePullbackIso φ ((moduleSpecΓFunctor (R := R)).obj
          ((Scheme.Modules.pushforward f).obj M))).hom).app ⊤
          (tilde.toOpen ((moduleSpecΓFunctor (R := R)).obj
            ((Scheme.Modules.pushforward f).obj M)) ⊤ m))
  have hc (P : (Spec R).Modules) (x : (moduleSpecΓFunctor (R := R)).obj P) :
      P.fromTildeΓ.app ⊤ (tilde.toOpen ((moduleSpecΓFunctor (R := R)).obj P) ⊤ x) = x := by
    have h := ConcreteCategory.congr_hom (Scheme.Modules.toOpen_fromTildeΓ_app P ⊤) x
    change P.fromTildeΓ.app ⊤
      (tilde.toOpen ((moduleSpecΓFunctor (R := R)).obj P) ⊤ x) =
        P.presheaf.map (homOfLE (le_refl ⊤)).op x at h
    simpa using h
  rw [hc, pushforwardBaseChange_adjoint_app_top,
    tildePullbackIso_adjoint_toOpen_top]
  unfold affineDirectImageTildeMap
  change sectionsBaseChangeMap φ f f' g w M m =
    ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g).obj M)).fromTildeΓ.app ⊤
      ((tilde.map (scalarSectionsBaseChangeMap φ f f' g w M)).app ⊤
        (tilde.toOpen _ ⊤ ((1 : T) ⊗ₜ[R,φ.hom] m)))
  have hm := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (scalarSectionsBaseChangeMap φ f f' g w M) ⊤)
      ((1 : T) ⊗ₜ[R,φ.hom] m)
  change (tilde.map (scalarSectionsBaseChangeMap φ f f' g w M)).app ⊤
      (tilde.toOpen _ ⊤ ((1 : T) ⊗ₜ[R,φ.hom] m)) =
    tilde.toOpen _ ⊤
      ((scalarSectionsBaseChangeMap φ f f' g w M) ((1 : T) ⊗ₜ[R,φ.hom] m)) at hm
  dsimp only [relativeGlobalSections, Functor.comp_obj] at *
  rw [hm]
  have hcT (P : (Spec T).Modules) (x : (moduleSpecΓFunctor (R := T)).obj P) :
      P.fromTildeΓ.app ⊤ (tilde.toOpen ((moduleSpecΓFunctor (R := T)).obj P) ⊤ x) = x := by
    have h := ConcreteCategory.congr_hom (Scheme.Modules.toOpen_fromTildeΓ_app P ⊤) x
    change P.fromTildeΓ.app ⊤
      (tilde.toOpen ((moduleSpecΓFunctor (R := T)).obj P) ⊤ x) =
        P.presheaf.map (homOfLE (le_refl ⊤)).op x at h
    simpa using h
  rw [hcT]
  exact (scalarSectionsBaseChangeMap_one_tmul φ f f' g w M m).symm

/-- For quasi-coherent direct images over spectra, an invertible scalar comparison
makes the specified sheaf base-change comparison invertible. -/
theorem isIso_pushforwardBaseChange_of_isIso_scalarSectionsBaseChangeMap
    (M : X.Modules) [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    [((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g).obj M)).IsQuasicoherent]
    [IsIso (scalarSectionsBaseChangeMap φ f f' g w M)] :
    IsIso (pushforwardBaseChange (Spec.map φ) f f' g w M) := by
  let P := (Scheme.Modules.pushforward f).obj M
  let Q := (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g).obj M)
  let : IsIso P.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent P
  let : IsIso Q.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent Q
  let : IsIso (tilde.map (scalarSectionsBaseChangeMap φ f f' g w M)) :=
    inferInstanceAs (IsIso ((tilde.functor T).map (scalarSectionsBaseChangeMap φ f f' g w M)))
  have h : IsIso ((Scheme.Modules.pullback (Spec.map φ)).map
      ((Scheme.Modules.pushforward f).obj M).fromTildeΓ ≫
        pushforwardBaseChange (Spec.map φ) f f' g w M) := by
    rw [pullback_fromTildeΓ_comp_pushforwardBaseChange]
    unfold affineDirectImageTildeMap
    infer_instance
  let : IsIso ((Scheme.Modules.pullback (Spec.map φ)).map P.fromTildeΓ) := inferInstance
  exact IsIso.of_isIso_comp_left ((Scheme.Modules.pullback (Spec.map φ)).map P.fromTildeΓ) _

end Langlands.AlgebraicGeometry.Modules.DerivedSections
