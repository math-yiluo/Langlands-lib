import Langlands.AlgebraicGeometry.Modules.SectionLocus
import Langlands.AlgebraicGeometry.Modules.Tensor

/-! # Tensor products of global module-sheaf sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Langlands.Scheme.Modules

namespace Langlands.SchemeModule

variable {X : Scheme.{u}}

/-- The two existing names for the structure module have the same definition. -/
lemma structureModule_eq_structureSheaf (X : Scheme.{u}) :
    structureModule X = structureSheaf X := rfl

private lemma sectionFamily_top (M : X.Modules) (s : GlobalSections M) :
    (sectionFamily M s).val (.op ⊤) = s := by
  change M.presheaf.map (𝟙 _) s = s
  simp

private lemma sectionFamily_eval (M : X.Modules) (s : M.sections) :
    sectionFamily M (s.val (.op ⊤)) = s := by
  apply PresheafOfModules.sections_ext
  intro U
  exact s.property (homOfLE (show U.unop ≤ ⊤ from le_top)).op

/-- A global section is equivalently a morphism from the actual structure module. -/
def sectionHomEquiv (M : X.Modules) :
    GlobalSections M ≃ (structureModule X ⟶ M) where
  toFun := sectionHom M
  invFun f := (M.unitHomEquiv f).val (.op ⊤)
  left_inv s := by
    change (M.unitHomEquiv (M.unitHomEquiv.symm (sectionFamily M s))).val _ = s
    rw [Equiv.apply_symm_apply]
    exact sectionFamily_top M s
  right_inv f := by
    apply M.unitHomEquiv.injective
    change M.unitHomEquiv (M.unitHomEquiv.symm _) = M.unitHomEquiv f
    rw [Equiv.apply_symm_apply, sectionFamily_eval]

/-- The section morphism determines its global section. -/
lemma sectionHom_injective (M : X.Modules) :
    Function.Injective (sectionHom M) :=
  (sectionHomEquiv M).injective

/-- On an open, the section morphism sends one to the restriction of the section. -/
@[simp]
lemma sectionHom_app_one (M : X.Modules) (s : GlobalSections M) (U : X.Opens) :
    (sectionHom M s).app U (1 : Γ(X, U)) =
      M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s := by
  change (M.unitHomEquiv (M.unitHomEquiv.symm (sectionFamily M s))).val (.op U) = _
  rw [Equiv.apply_symm_apply]
  rfl

namespace LineBundleDescent

variable (M : X.Modules)

lemma sectionHom_app (s : GlobalSections M) (U : X.Opens) (a : Γ(X, U)) :
    (sectionHom M s).app U a =
      a • M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s := by
  have h := Scheme.Modules.Hom.app_smul (sectionHom M s) a
    (show Γ(structureModule X, U) from (1 : Γ(X, U)))
  have e : (a • (show Γ(structureModule X, U) from (1 : Γ(X, U))) : Γ(structureModule X, U)) =
      (show Γ(structureModule X, U) from a) := mul_one a
  rw [e] at h
  rw [h]
  exact congrArg (a • ·) (sectionHom_app_one M s U)

end LineBundleDescent


/-- Section morphisms commute with maps of module sheaves. -/
@[simp]
lemma sectionHom_naturality {M N : X.Modules} (f : M ⟶ N) (s : GlobalSections M) :
    sectionHom N (f.app ⊤ s) = sectionHom M s ≫ f := by
  apply N.unitHomEquiv.injective
  change N.unitHomEquiv (N.unitHomEquiv.symm _) = _
  rw [Equiv.apply_symm_apply]
  change sectionFamily N (f.app ⊤ s) =
    SheafOfModules.sectionsMap f (M.unitHomEquiv (M.unitHomEquiv.symm _))
  rw [Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro U
  exact (PresheafOfModules.naturality_apply f.val
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op s).symm

/-- The tensor product of two actual global sections. -/
def tensorSection (M N : X.Modules) (s : GlobalSections M) (t : GlobalSections N) :
    GlobalSections (tensorObj M N) :=
  (sectionHomEquiv (tensorObj M N)).symm
    ((tensorLeftUnitor (structureSheaf X)).inv ≫
      tensorMap (sectionHom M s) (sectionHom N t))

/-- The product section is characterized by the tensor of its section morphisms. -/
@[simp]
lemma sectionHom_tensorSection (M N : X.Modules)
    (s : GlobalSections M) (t : GlobalSections N) :
    sectionHom (tensorObj M N) (tensorSection M N s t) =
      (tensorLeftUnitor (structureSheaf X)).inv ≫
        tensorMap (sectionHom M s) (sectionHom N t) :=
  (sectionHomEquiv (tensorObj M N)).apply_symm_apply _

/-- Tensoring sections commutes with maps in both module factors. -/
lemma tensorSection_naturality {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') (s : GlobalSections M) (t : GlobalSections N) :
    (tensorMap f g).app ⊤ (tensorSection M N s t) =
      tensorSection M' N' (f.app ⊤ s) (g.app ⊤ t) := by
  apply sectionHom_injective (tensorObj M' N')
  rw [sectionHom_naturality, sectionHom_tensorSection, sectionHom_tensorSection,
    sectionHom_naturality, sectionHom_naturality]
  let a : structureSheaf X ⟶ M := sectionHom M s
  let b : structureSheaf X ⟶ N := sectionHom N t
  let δ : structureSheaf X ⟶ tensorObj (structureSheaf X) (structureSheaf X) :=
    (tensorLeftUnitor (structureSheaf X)).inv
  change (δ ≫ tensorMap a b) ≫ tensorMap f g =
    δ ≫ tensorMap (a ≫ f) (b ≫ g)
  rw [Category.assoc]
  congr 1
  exact ((tensorFunctor X).map_comp
    (X := (structureSheaf X, structureSheaf X)) (Y := (M, N)) (Z := (M', N'))
    (a, b) (f, g)).symm

/-- Evaluation on an open is obtained by evaluating the tensor of section morphisms. -/
lemma tensorSection_restrict (M N : X.Modules)
    (s : GlobalSections M) (t : GlobalSections N) (U : X.Opens) :
    (tensorObj M N).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (tensorSection M N s t) =
      (tensorMap (sectionHom M s) (sectionHom N t)).app U
        ((tensorLeftUnitor (structureSheaf X)).inv.app U (1 : Γ(X, U))) := by
  have h := congrArg
    (fun f : structureModule X ⟶ tensorObj M N ↦ f.app U (1 : Γ(X, U)))
    (sectionHom_tensorSection M N s t)
  exact (sectionHom_app_one (tensorObj M N) (tensorSection M N s t) U).symm.trans h

end Langlands.SchemeModule
