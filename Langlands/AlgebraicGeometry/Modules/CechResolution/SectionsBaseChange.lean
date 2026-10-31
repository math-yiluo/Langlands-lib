import Langlands.AlgebraicGeometry.Modules.CechResolution.BaseChange
import Langlands.AlgebraicGeometry.Modules.BaseChangeResolutionExactScalars
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Scalar sections maps on sheafified Čech complexes -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open scoped TensorProduct ChangeOfRings

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

local instance moduleHasBiproduct {T : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (B : ι → ModuleCat.{u} T) : HasBiproduct B :=
  HasBiproduct.of_hasProduct B

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (f : X ⟶ Spec R) (f' : Y ⟶ Spec S)
  (g : Y ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
  {M : X.Modules} {N : Y.Modules}
  (a : M ⟶ (Scheme.Modules.pushforward g).obj N)

/-- The ordinary relative sections map on one open factor. -/
def factorSectionsMap {W : X.Opens} {W' : Y.Opens} (hW : W' ≤ g ⁻¹ᵁ W) :
    (relativeGlobalSections f).obj (sheafOn M W) ⟶
      (ModuleCat.restrictScalars φ.hom).obj
        ((relativeGlobalSections f').obj (sheafOn N W')) :=
  (relativeGlobalSections f).map (sheafOnPushforward g a hW) ≫
    (relativeGlobalSectionsCompIso g f).hom.app (sheafOn N W') ≫
    (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w).inv.app (sheafOn N W')

/-- The scalar-linear adjunct of the actual map on an open factor. -/
def scalarFactorSectionsMap {W : X.Opens} {W' : Y.Opens} (hW : W' ≤ g ⁻¹ᵁ W) :
    (ModuleCat.extendScalars φ.hom).obj
        ((relativeGlobalSections f).obj (sheafOn M W)) ⟶
      (relativeGlobalSections f').obj (sheafOn N W') :=
  ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm
    (factorSectionsMap φ f f' g w a hW)

lemma scalarFactorSectionsMap_one_tmul {W : X.Opens} {W' : Y.Opens}
    (hW : W' ≤ g ⁻¹ᵁ W)
    (x : (relativeGlobalSections f).obj (sheafOn M W)) :
    scalarFactorSectionsMap φ f f' g w a hW ((1 : S) ⊗ₜ[R,φ.hom] x) =
      factorSectionsMap φ f f' g w a hW x := by
  have h := congrArg (fun k => k x)
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).apply_symm_apply
      (factorSectionsMap φ f f' g w a hW))
  simpa only [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] using! h

/-- Relative sections preserve finite biproducts, with the existing choices
of biproduct in the module category. -/
def sectionsBiproductIso {ι : Type u} [Fintype ι] (B : ι → X.Modules) :
    (relativeGlobalSections f).obj (⨁ B) ≅
      ⨁ (fun i => (relativeGlobalSections f).obj (B i)) := by
  have h := biproduct.isLimit (fun i => (relativeGlobalSections f).obj (B i))
  letI : (relativeGlobalSections f).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor).IsRightAdjoint
  letI : PreservesBiproduct B (relativeGlobalSections f) :=
    preservesBiproduct_of_preservesProduct _
  exact (isBilimitOfPreserves (relativeGlobalSections f)
    (biproduct.isBilimit B)).isLimit.conePointUniqueUpToIso h

@[reassoc (attr := simp)]
lemma sectionsBiproductIso_hom_π {ι : Type u} [Fintype ι]
    (B : ι → X.Modules) (i : ι) :
    (sectionsBiproductIso f B).hom ≫
        biproduct.π (fun i => (relativeGlobalSections f).obj (B i)) i =
      (relativeGlobalSections f).map (biproduct.π B i) := by
  dsimp only [sectionsBiproductIso]
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk i)

/-- Scalar extension of relative sections preserves finite biproducts,
using the existing choices in both module categories. -/
def scalarSectionsBiproductIso {ι : Type u} [Fintype ι] (B : ι → X.Modules) :
    (ModuleCat.extendScalars φ.hom).obj ((relativeGlobalSections f).obj (⨁ B)) ≅
      ⨁ (fun i => (ModuleCat.extendScalars φ.hom).obj
        ((relativeGlobalSections f).obj (B i))) := by
  have h := biproduct.isLimit (fun i => (ModuleCat.extendScalars φ.hom).obj
    ((relativeGlobalSections f).obj (B i)))
  letI : (relativeGlobalSections f).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor).IsRightAdjoint
  letI : PreservesBiproduct B (relativeGlobalSections f) :=
    preservesBiproduct_of_preservesProduct _
  letI : PreservesBiproduct ((relativeGlobalSections f).obj ∘ B)
      (ModuleCat.extendScalars φ.hom) :=
    preservesBiproduct_of_preservesCoproduct _
  exact (isBilimitOfPreserves (ModuleCat.extendScalars φ.hom)
    (isBilimitOfPreserves (relativeGlobalSections f)
      (biproduct.isBilimit B))).isLimit.conePointUniqueUpToIso h

@[reassoc (attr := simp)]
lemma scalarSectionsBiproductIso_hom_π {ι : Type u} [Fintype ι]
    (B : ι → X.Modules) (i : ι) :
    (scalarSectionsBiproductIso φ f B).hom ≫
        biproduct.π (fun i => (ModuleCat.extendScalars φ.hom).obj
          ((relativeGlobalSections f).obj (B i))) i =
      (ModuleCat.extendScalars φ.hom).map
        ((relativeGlobalSections f).map (biproduct.π B i)) := by
  dsimp only [scalarSectionsBiproductIso]
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk i)

section Cover

variable [IsAffineHom g] (𝒰 : X.OrderedAffineCover)

/-- The actual scalar sections cochain map for the induced Čech map. -/
abbrev scalarCechSectionsMap :
    ((ModuleCat.extendScalars φ.hom).mapHomologicalComplex _).obj
        (((relativeGlobalSections f).mapHomologicalComplex _).obj (cechComplex 𝒰 M)) ⟶
      ((relativeGlobalSections f').mapHomologicalComplex _).obj
        (cechComplex (inverseImageCover g 𝒰) N) :=
  scalarResolutionSectionsBaseChangeMap φ f f' g w (cechPushforward g a 𝒰)

/-- Projection onto an intersection factor commutes with the actual scalar map. -/
@[reassoc]
lemma scalarCechSectionsMap_f_π (p : ℕ) (s : 𝒰.Idx p) :
    (scalarCechSectionsMap φ f f' g w a 𝒰).f p ≫
        (relativeGlobalSections f').map
          (biproduct.π (fun s : 𝒰.Idx p =>
            sheafOn N ((inverseImageCover g 𝒰).inter s)) s) =
      (ModuleCat.extendScalars φ.hom).map
        ((relativeGlobalSections f).map
          (biproduct.π (fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s)) s)) ≫
        scalarFactorSectionsMap φ f f' g w a (inverseImageCover_inter_le g 𝒰 s) := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
  simp only [scalarCechSectionsMap, scalarResolutionSectionsBaseChangeMap_f,
    scalarFactorSectionsMap, Equiv.apply_symm_apply, resolutionSectionsBaseChangeMap_f,
    cechPushforward_f, factorSectionsMap]
  have hcomp := (relativeGlobalSectionsCompIso g f).hom.naturality
    (biproduct.π (fun s : 𝒰.Idx p =>
      sheafOn N ((inverseImageCover g 𝒰).inter s)) s)
  have hbase := (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w).inv.naturality
    (biproduct.π (fun s : 𝒰.Idx p =>
      sheafOn N ((inverseImageCover g 𝒰).inter s)) s)
  dsimp only [Functor.comp_map] at hcomp hbase
  let F := relativeGlobalSections f
  let P := biproduct.π (fun s : 𝒰.Idx p =>
    sheafOn N ((inverseImageCover g 𝒰).inter s)) s
  let c := (relativeGlobalSectionsCompIso g f).hom
  let b := (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w).inv
  calc
    _ = F.map (cechTermPushforward g a 𝒰 p) ≫
        c.app (cechTerm (inverseImageCover g 𝒰) N p) ≫
        (relativeGlobalSections (g ≫ f)).map P ≫
        b.app (sheafOn N ((inverseImageCover g 𝒰).inter s)) := by
      simpa only [Category.assoc] using!
        congrArg (fun k => F.map (cechTermPushforward g a 𝒰 p) ≫
          c.app (cechTerm (inverseImageCover g 𝒰) N p) ≫ k) hbase.symm
    _ = (F.map (cechTermPushforward g a 𝒰 p) ≫
        F.map ((Scheme.Modules.pushforward g).map P)) ≫
        c.app (sheafOn N ((inverseImageCover g 𝒰).inter s)) ≫
        b.app (sheafOn N ((inverseImageCover g 𝒰).inter s)) := by
      simpa only [Category.assoc] using!
        congrArg (fun k => F.map (cechTermPushforward g a 𝒰 p) ≫ k ≫
          b.app (sheafOn N ((inverseImageCover g 𝒰).inter s))) hcomp.symm
    _ = _ := by
      have hπ := congrArg (fun k => F.map k ≫
        c.app (sheafOn N ((inverseImageCover g 𝒰).inter s)) ≫
        b.app (sheafOn N ((inverseImageCover g 𝒰).inter s)))
          (cechTermPushforward_π g a 𝒰 p s)
      simpa only [Functor.map_comp, Category.assoc] using! hπ

/-- The actual degree map is the biproduct of its factor maps through the
canonical finite-biproduct identifications. -/
lemma scalarCechSectionsMap_f_biproduct (p : ℕ) :
    (scalarCechSectionsMap φ f f' g w a 𝒰).f p ≫
        (sectionsBiproductIso f' (fun s : 𝒰.Idx p =>
          sheafOn N ((inverseImageCover g 𝒰).inter s))).hom =
      (scalarSectionsBiproductIso φ f
        (fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s))).hom ≫
        biproduct.map (fun s : 𝒰.Idx p =>
          scalarFactorSectionsMap φ f f' g w a (inverseImageCover_inter_le g 𝒰 s)) := by
  apply biproduct.hom_ext
  intro s
  simp only [Category.assoc, sectionsBiproductIso_hom_π, biproduct.map_π,
    scalarSectionsBiproductIso_hom_π_assoc, scalarCechSectionsMap_f_π]

/-- Invertibility of the factor maps implies invertibility in each degree. -/
lemma isIso_scalarCechSectionsMap_f_of_factors (p : ℕ)
    (h : ∀ s : 𝒰.Idx p, IsIso
      (scalarFactorSectionsMap φ f f' g w a (inverseImageCover_inter_le g 𝒰 s))) :
    IsIso ((scalarCechSectionsMap φ f f' g w a 𝒰).f p) := by
  let := h
  let e := biproduct.mapIso (fun s : 𝒰.Idx p =>
    asIso (scalarFactorSectionsMap φ f f' g w a (inverseImageCover_inter_le g 𝒰 s)))
  have : IsIso (biproduct.map (fun s : 𝒰.Idx p =>
      scalarFactorSectionsMap φ f f' g w a (inverseImageCover_inter_le g 𝒰 s))) :=
    e.isIso_hom
  have : IsIso ((scalarCechSectionsMap φ f f' g w a 𝒰).f p ≫
      (sectionsBiproductIso f' (fun s : 𝒰.Idx p =>
        sheafOn N ((inverseImageCover g 𝒰).inter s))).hom) := by
    rw [scalarCechSectionsMap_f_biproduct]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (sectionsBiproductIso f'
    (fun s : 𝒰.Idx p => sheafOn N ((inverseImageCover g 𝒰).inter s))).hom

/-- The actual scalar cochain map is invertible if all factor maps are. -/
lemma isIso_scalarCechSectionsMap_of_factors
    (h : ∀ (p : ℕ) (s : 𝒰.Idx p), IsIso
      (scalarFactorSectionsMap φ f f' g w a (inverseImageCover_inter_le g 𝒰 s))) :
    IsIso (scalarCechSectionsMap φ f f' g w a 𝒰) := by
  let (p : ℕ) : IsIso ((scalarCechSectionsMap φ f f' g w a 𝒰).f p) :=
    isIso_scalarCechSectionsMap_f_of_factors φ f f' g w a 𝒰 p (h p)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Factorwise invertibility also gives the quasi-isomorphism used by
the canonical flat base-change comparison. -/
lemma quasiIso_scalarCechSectionsMap_of_factors
    (h : ∀ (p : ℕ) (s : 𝒰.Idx p), IsIso
      (scalarFactorSectionsMap φ f f' g w a (inverseImageCover_inter_le g 𝒰 s))) :
    QuasiIso (scalarCechSectionsMap φ f f' g w a 𝒰) := by
  let := isIso_scalarCechSectionsMap_of_factors φ f f' g w a 𝒰 h
  infer_instance

end Cover

end Langlands.AlgebraicGeometry.Modules.CechResolution
