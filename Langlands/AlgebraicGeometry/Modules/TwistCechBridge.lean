import Langlands.AlgebraicGeometry.Modules.CechHSuccBridge
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2

/-! # Comparing FLT presheaf tensor products with sections of tensor products of modules -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory TensorProduct

namespace Langlands.AlgebraicGeometry.Modules.CechBridge

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {q : X ⟶ Spec (CommRingCat.of A)}

/-- The sectionwise map `Γ(F, U) ⊗ Γ(M, U) → Γ(F ⊗ M, U)` as a morphism of FLT presheaves on
affine opens. -/
def tensorSectionsAffHom (F M : X.Modules) :
    OModulePresheaf.AffHom ((OModulePresheaf.ofModules q F).tensor (OModulePresheaf.ofModules q M))
      (OModulePresheaf.ofModules q (F ⊗ M)) where
  app U :=
    { toFun := fun t => TensorProduct.lift (Scheme.Modules.tensorSectionsBilin F M U.1) t
      map_add' := map_add _
      map_smul' := fun r t => by
        let := Scheme.TwoAffineOpenCover.algebraOfHom q U.1
        change TensorProduct.lift (Scheme.Modules.tensorSectionsBilin F M U.1)
            (algebraMap A Γ(X, U.1) r • t) =
          algebraMap A Γ(X, U.1) r • TensorProduct.lift (Scheme.Modules.tensorSectionsBilin F M U.1) t
        exact map_smul _ _ _ }
  app_smul U a x := (TensorProduct.lift (Scheme.Modules.tensorSectionsBilin F M U.1)).map_smul a x
  naturality {U U'} h := by
    refine LinearMap.ext fun t => ?_
    change TensorProduct.lift (Scheme.Modules.tensorSectionsBilin F M U.1)
        ((OModulePresheaf.ofModules q F).tensorResₛₗ (OModulePresheaf.ofModules q M) h t) =
      (F ⊗ M).presheaf.map (homOfLE h).op
        (TensorProduct.lift (Scheme.Modules.tensorSectionsBilin F M U'.1) t)
    induction t using TensorProduct.inductionOn with
    | tmul x y => exact (Scheme.Modules.map_homOfLE_tensorSections h x y).symm
    | add s t hs ht =>
      exact (congrArg _ (map_add _ s t)).trans ((map_add _ _ _).trans
        ((congrArg₂ (· + ·) hs ht).trans ((map_add _ _ _).symm.trans
          (congrArg _ (map_add _ s t).symm))))

lemma tensorSectionsAffHom_bijective {F M : X.Modules} (hF : Scheme.Modules.IsInvertible F)
    (hM : Scheme.Modules.IsInvertible M) (U : X.affineOpens) :
    Function.Bijective ((tensorSectionsAffHom (q := q) F M).app U) :=
  hF.bijective_lift_tensorSectionsBilin_monoidalV2 hM U

/-- Tensoring a natural family of section maps `G(U) → H(U)` on the right gives a morphism of FLT
presheaf tensor products on affine opens. -/
def tensorRightAffHom (F' G H : OModulePresheaf q)
    (e : ∀ U : X.Opens, G.obj U →ₗ[Γ(X, U)] H.obj U)
    (he : ∀ {U U' : X.Opens} (h : U ≤ U') (x : G.obj U'), e U (G.res h x) = H.res h (e U' x)) :
    OModulePresheaf.AffHom (F'.tensor G) (F'.tensor H) where
  app U :=
    { toFun := fun t => LinearMap.lTensor (F'.obj U.1) (e U.1) t
      map_add' := map_add _
      map_smul' := fun r t => by
        let := Scheme.TwoAffineOpenCover.algebraOfHom q U.1
        change LinearMap.lTensor (F'.obj U.1) (e U.1) (algebraMap A Γ(X, U.1) r • t) =
          algebraMap A Γ(X, U.1) r • LinearMap.lTensor (F'.obj U.1) (e U.1) t
        exact map_smul _ _ _ }
  app_smul U a x := (LinearMap.lTensor (F'.obj U.1) (e U.1)).map_smul a x
  naturality {U U'} h := by
    refine LinearMap.ext fun t => ?_
    change LinearMap.lTensor (F'.obj U.1) (e U.1) (F'.tensorResₛₗ G h t) =
      F'.tensorResₛₗ H h (LinearMap.lTensor (F'.obj U'.1) (e U'.1) t)
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      change F'.res h x ⊗ₜ e U.1 (G.res h y) = F'.res h x ⊗ₜ H.res h (e U'.1 y)
      rw [he]
    | add s t hs ht =>
      exact (congrArg _ (map_add _ s t)).trans ((map_add _ _ _).trans
        ((congrArg₂ (· + ·) hs ht).trans ((map_add _ _ _).symm.trans
          (congrArg _ (map_add _ s t).symm))))

lemma tensorRightAffHom_bijective (F' G H : OModulePresheaf q)
    (e : ∀ U : X.Opens, G.obj U →ₗ[Γ(X, U)] H.obj U)
    (he : ∀ {U U' : X.Opens} (h : U ≤ U') (x : G.obj U'), e U (G.res h x) = H.res h (e U' x))
    (U : X.affineOpens) (hU : Function.Bijective (e U.1)) :
    Function.Bijective ((tensorRightAffHom F' G H e he).app U) :=
  (LinearEquiv.lTensor (F'.obj U.1) (LinearEquiv.ofBijective (e U.1) hU)).bijective

end Langlands.AlgebraicGeometry.Modules.CechBridge
