/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-!
# Global sections of the internal hom of `𝒪_X`-modules

The global sections of the internal hom `Hom(M, N)` of two `𝒪_X`-modules are the morphisms
`M ⟶ N`, naturally in `M`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A morphism `M ⟶ N` of `𝒪_X`-modules, as a global section of the internal hom `Hom(M, N)`. -/
def homToΓHomObj (M N : X.Modules) :
    (M ⟶ N) →+ Γ(SheafOfModules.homObj (R := X.sheaf) M N, ⊤) where
  toFun φ := (PresheafOfModules.restrictOver _ ⊤).map φ.val
  map_zero' := rfl
  map_add' _ _ := rfl

lemma homToΓHomObj_injective (M N : X.Modules) : Function.Injective (homToΓHomObj M N) := by
  intro φ ψ h
  ext U x
  exact congr(($h).app (op (Over.mk (homOfLE (le_top : U ≤ ⊤)))) x)

/-- The compatible family of restrictions of a global section of the internal hom. -/
def ΓHomObjSections {M N : X.Modules} (s : Γ(SheafOfModules.homObj (R := X.sheaf) M N, ⊤)) :
    (SheafOfModules.homObj (R := X.sheaf) M N).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ PresheafOfModules.restrictOverMap (homOfLE (le_top : U.unop ≤ ⊤)) s)
    fun U V f ↦ by
      change PresheafOfModules.restrictOverMap f.unop _ = _
      rw [← PresheafOfModules.restrictOverMap_comp]
      rfl

lemma homToΓHomObj_surjective (M N : X.Modules) : Function.Surjective (homToΓHomObj M N) := by
  intro s
  refine ⟨SheafOfModules.homObjSectionsEquiv M N (ΓHomObjSections s), ?_⟩
  refine PresheafOfModules.hom_ext fun W ↦ ?_
  ext x
  exact PresheafOfModules.restrictOver_hom_app_congr s (Subsingleton.elim _ _) x

/-- **Global sections of the internal hom**: `Γ(X, Hom(M, N)) ≃ Hom(M, N)`. -/
def ΓHomObjAddEquiv (M N : X.Modules) :
    Γ(SheafOfModules.homObj (R := X.sheaf) M N, ⊤) ≃+ (M ⟶ N) :=
  (AddEquiv.ofBijective (homToΓHomObj M N)
    ⟨homToΓHomObj_injective M N, homToΓHomObj_surjective M N⟩).symm

@[simp]
lemma homToΓHomObj_ΓHomObjAddEquiv {M N : X.Modules}
    (s : Γ(SheafOfModules.homObj (R := X.sheaf) M N, ⊤)) :
    homToΓHomObj M N (ΓHomObjAddEquiv M N s) = s :=
  (AddEquiv.ofBijective (homToΓHomObj M N)
    ⟨homToΓHomObj_injective M N, homToΓHomObj_surjective M N⟩).apply_symm_apply s

lemma homToΓHomObj_comp {M' M N : X.Modules} (f : M' ⟶ M) (φ : M ⟶ N) :
    homToΓHomObj M' N (f ≫ φ) =
      Hom.app (SheafOfModules.homObjMap (R := X.sheaf) f (𝟙 N)) ⊤ (homToΓHomObj M N φ) := by
  refine PresheafOfModules.hom_ext fun W ↦ ?_
  ext x
  rfl

lemma homToΓHomObj_comp_smulHom {M N : X.Modules} (φ : M ⟶ N) (r : Γ(X, ⊤)) :
    homToΓHomObj M N (φ ≫ N.smulHom r) = r • homToΓHomObj M N φ := by
  refine PresheafOfModules.hom_ext fun W ↦ ?_
  ext x
  rfl

lemma H.zeroLinearEquiv_map_homObj {M N : X.Modules} (φ : M ⟶ N) (x : M.H 0) :
    H.zeroLinearEquiv N (H.map φ 0 x) = φ.app ⊤ (H.zeroLinearEquiv M x) :=
  (Sheaf.H.equiv₀_naturality (hT := isTerminalTop)
    ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) x).symm

/-- **`H⁰` of the internal hom**: `H⁰(X, Hom(M, N)) ≃ Hom(M, N)`. -/
def homObjHZeroAddEquiv (M N : X.Modules) :
    H (X := X) (SheafOfModules.homObj (R := X.sheaf) M N) 0 ≃+ (M ⟶ N) :=
  (H.zeroLinearEquiv _).toAddEquiv.trans (ΓHomObjAddEquiv M N)

lemma homToΓHomObj_homObjHZeroAddEquiv {M N : X.Modules}
    (x : H (X := X) (SheafOfModules.homObj (R := X.sheaf) M N) 0) :
    homToΓHomObj M N (homObjHZeroAddEquiv M N x) = H.zeroLinearEquiv _ x :=
  homToΓHomObj_ΓHomObjAddEquiv _

/-- `homObjHZeroAddEquiv` is natural in the source. -/
lemma homObjHZeroAddEquiv_map {M' M N : X.Modules} (f : M' ⟶ M)
    (x : H (X := X) (SheafOfModules.homObj (R := X.sheaf) M N) 0) :
    homObjHZeroAddEquiv M' N (H.map (SheafOfModules.homObjMap (R := X.sheaf) f (𝟙 N)) 0 x) =
      f ≫ homObjHZeroAddEquiv M N x := by
  apply homToΓHomObj_injective
  rw [homToΓHomObj_homObjHZeroAddEquiv, homToΓHomObj_comp, homToΓHomObj_homObjHZeroAddEquiv,
    H.zeroLinearEquiv_map_homObj]

/-- `homObjHZeroAddEquiv` turns multiplication by a global function into composition with the
multiplication on the target. -/
lemma homObjHZeroAddEquiv_smul {M N : X.Modules} (r : Γ(X, ⊤))
    (x : H (X := X) (SheafOfModules.homObj (R := X.sheaf) M N) 0) :
    homObjHZeroAddEquiv M N (r • x) = homObjHZeroAddEquiv M N x ≫ N.smulHom r := by
  apply homToΓHomObj_injective
  rw [homToΓHomObj_homObjHZeroAddEquiv, homToΓHomObj_comp_smulHom,
    homToΓHomObj_homObjHZeroAddEquiv, LinearEquiv.map_smul]

end AlgebraicGeometry.Scheme.Modules
