import Langlands.AlgebraicGeometry.Modules.TildePullback

/-! # Canonical scalar extension of affine global sections -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace Langlands.Scheme.Modules

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The semilinear map on affine sections induced by the actual pullback unit. -/
def affineSectionsPullbackMap (M : (Spec R).Modules) :
    (moduleSpecΓFunctor (R := R)).obj M ⟶
      (ModuleCat.restrictScalars φ.hom).obj
        ((moduleSpecΓFunctor (R := S)).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).obj M)) :=
  (moduleSpecΓFunctor (R := R)).map
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
    (pushforwardΓIso φ).hom.app _

/-- The scalar-linear adjunct of the pullback map on affine sections. -/
def affineScalarSectionsMap (M : (Spec R).Modules) :
    (ModuleCat.extendScalars φ.hom).obj ((moduleSpecΓFunctor (R := R)).obj M) ⟶
      (moduleSpecΓFunctor (R := S)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).obj M) :=
  ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm
    (affineSectionsPullbackMap φ M)

@[simp]
lemma affineScalarSectionsMap_homEquiv (M : (Spec R).Modules) :
    (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _
        (affineScalarSectionsMap φ M) = affineSectionsPullbackMap φ M := by
  simp [affineScalarSectionsMap]

/-- The unit formula fixes the canonical map, independently of a tilde presentation. -/
@[reassoc]
lemma affineScalarSectionsMap_unit (M : (Spec R).Modules) :
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app
        ((moduleSpecΓFunctor (R := R)).obj M) ≫
        (ModuleCat.restrictScalars φ.hom).map (affineScalarSectionsMap φ M) =
      affineSectionsPullbackMap φ M := by
  simpa only [Adjunction.homEquiv_unit] using affineScalarSectionsMap_homEquiv φ M

lemma affineScalarSectionsMap_one_tmul (M : (Spec R).Modules)
    (m : (moduleSpecΓFunctor (R := R)).obj M) :
    affineScalarSectionsMap φ M ((1 : S) ⊗ₜ[R,φ.hom] m) =
      affineSectionsPullbackMap φ M m := by
  have h := congrArg (fun k => k m) (affineScalarSectionsMap_homEquiv φ M)
  simpa only [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] using h

/-- Naturality with respect to an arbitrary morphism of coefficient sheaves. -/
@[reassoc]
lemma affineScalarSectionsMap_naturality {M N : (Spec R).Modules} (a : M ⟶ N) :
    (ModuleCat.extendScalars φ.hom).map ((moduleSpecΓFunctor (R := R)).map a) ≫
        affineScalarSectionsMap φ N =
      affineScalarSectionsMap φ M ≫ (moduleSpecΓFunctor (R := S)).map
        ((AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).map a) := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    affineScalarSectionsMap_homEquiv, affineScalarSectionsMap_homEquiv]
  unfold affineSectionsPullbackMap
  have hunit := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
    (Spec.map φ)).unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hunit
  rw [← Category.assoc, ← Functor.map_comp, hunit, Functor.map_comp, Category.assoc,
    Category.assoc]
  congr 1

/-- On an associated sheaf, the canonical section map is the existing tilde pullback
isomorphism, after the standard global-section identifications. -/
@[reassoc]
lemma affineScalarSectionsMap_tilde (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars φ.hom).map (tilde.isoTop M).hom ≫
        affineScalarSectionsMap φ (tilde M) ≫
        (moduleSpecΓFunctor (R := S)).map (tildePullbackIso φ M).hom =
      (tilde.isoTop ((ModuleCat.extendScalars φ.hom).obj M)).hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  simp only [ConcreteCategory.comp_apply, ModuleCat.ExtendScalars.map_tmul]
  have h := affineScalarSectionsMap_one_tmul φ (tilde M) ((tilde.isoTop M).hom m)
  calc
    _ = (moduleSpecΓFunctor (R := S)).map (tildePullbackIso φ M).hom
        (affineSectionsPullbackMap φ (tilde M) ((tilde.isoTop M).hom m)) :=
      congrArg ((moduleSpecΓFunctor (R := S)).map (tildePullbackIso φ M).hom) h
    _ = _ := tildePullbackIso_adjoint_toOpen_top φ M m

instance isIso_affineScalarSectionsMap_tilde (M : ModuleCat.{u} R) :
    IsIso (affineScalarSectionsMap φ (tilde M)) := by
  have h := affineScalarSectionsMap_tilde φ M
  have : IsIso ((ModuleCat.extendScalars φ.hom).map (tilde.isoTop M).hom ≫
      affineScalarSectionsMap φ (tilde M) ≫
      (moduleSpecΓFunctor (R := S)).map (tildePullbackIso φ M).hom) := by
    rw [h]
    infer_instance
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using this

/-- Canonical scalar extension commutes with affine sections of a quasi-coherent sheaf.
No flatness assumption is needed. -/
instance isIso_affineScalarSectionsMap (M : (Spec R).Modules) [M.IsQuasicoherent] :
    IsIso (affineScalarSectionsMap φ M) := by
  have h := affineScalarSectionsMap_naturality φ M.fromTildeΓ
  have : IsIso ((ModuleCat.extendScalars φ.hom).map
      ((moduleSpecΓFunctor (R := R)).map M.fromTildeΓ) ≫
      affineScalarSectionsMap φ M) := by
    rw [h]
    infer_instance
  simpa only [isIso_comp_left_iff] using this

/-- The affine sections base-change isomorphism has the canonical unit-induced map as
its forward morphism. -/
def affineScalarSectionsIso (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars φ.hom).obj ((moduleSpecΓFunctor (R := R)).obj M) ≅
      (moduleSpecΓFunctor (R := S)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).obj M) :=
  asIso (affineScalarSectionsMap φ M)

end Langlands.Scheme.Modules
