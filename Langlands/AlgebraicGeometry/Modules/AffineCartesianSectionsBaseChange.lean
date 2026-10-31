import Langlands.AlgebraicGeometry.Modules.SectionsBaseChangeIso
import Langlands.AlgebraicGeometry.Modules.PushoutCohomologyBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Canonical scalar sections base change on Cartesian affine squares -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

section Rings

variable {R S A B : CommRingCat.{u}}
  (φ : R ⟶ S) (α : R ⟶ A) (β : S ⟶ B) (γ : A ⟶ B)

/-- Ring pushouts give invertibility of the actual scalar sections map. -/
lemma isIso_scalarSectionsBaseChangeMap_of_isPushout
    (h : IsPushout φ α β γ) (M : (Spec A).Modules) [M.IsQuasicoherent] :
    IsIso (scalarSectionsBaseChangeMap φ (Spec.map α) (Spec.map β) (Spec.map γ)
      (by rw [← Spec.map_comp, ← Spec.map_comp, h.w]) M) := by
  let : Algebra R S := φ.hom.toAlgebra
  let : Algebra R A := α.hom.toAlgebra
  let : Algebra S B := β.hom.toAlgebra
  let : Algebra A B := γ.hom.toAlgebra
  let : Algebra R B := (φ ≫ β).hom.toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  let : Algebra.IsPushout R S A B := CommRingCat.isPushout_iff_isPushout.mp h
  have hi := Langlands.Scheme.Modules.isIso_pushoutAffineScalarSectionsMap R S A B M
  rw [← scalarSectionsBaseChangeMap_affineAlgebraSquare R S A B M] at hi
  exact hi

/-- The Cartesian square of spectra is a pushout square of its rings. -/
lemma isPushout_of_isPullback_spec
    (h : IsPullback (Spec.map γ) (Spec.map β) (Spec.map α) (Spec.map φ)) :
    IsPushout φ α β γ := by
  exact (IsPullback.of_map_of_faithful Scheme.Spec h).unop

/-- A Cartesian square between specified spectra has invertible scalar sections map. -/
lemma isIso_scalarSectionsBaseChangeMap_of_isPullback_spectra
    (f : Spec A ⟶ Spec R) (f' : Spec B ⟶ Spec S) (g : Spec B ⟶ Spec A)
    (w : g ≫ f = f' ≫ Spec.map φ)
    (h : IsPullback g f' f (Spec.map φ))
    (M : (Spec A).Modules) [M.IsQuasicoherent] :
    IsIso (scalarSectionsBaseChangeMap φ f f' g w M) := by
  obtain ⟨α, rfl⟩ : ∃ α, Spec.map α = f := ⟨_, Spec.map_preimage f⟩
  obtain ⟨β, rfl⟩ : ∃ β, Spec.map β = f' := ⟨_, Spec.map_preimage f'⟩
  obtain ⟨γ, rfl⟩ : ∃ γ, Spec.map γ = g := ⟨_, Spec.map_preimage g⟩
  exact isIso_scalarSectionsBaseChangeMap_of_isPushout φ α β γ
    (isPushout_of_isPullback_spec φ α β γ h) M

end Rings

section Transport

variable {X Y Z : Scheme.{u}} {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (f : X ⟶ Spec R) (f' : Y ⟶ Spec S)
  (g : Y ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)

/-- Invertibility can be detected after an isomorphic presentation of the target. -/
lemma isIso_scalarSectionsBaseChangeMap_of_precomp_iso
    (h : Z ⟶ Y) [IsIso h] (M : X.Modules)
    (hi : IsIso (scalarSectionsBaseChangeMap φ f (h ≫ f') (h ≫ g)
      (by simp only [Category.assoc, w]) M)) :
    IsIso (scalarSectionsBaseChangeMap φ f f' g w M) := by
  let q := scalarSectionsBaseChangeMap φ f f' g w M
  let t := scalarSectionsBaseChangeMap (𝟙 S) f' (h ≫ f') h (by simp)
    ((Scheme.Modules.pullback g).obj M)
  let c := (relativeGlobalSections (h ≫ f')).map
    ((Scheme.Modules.pullbackComp h g).hom.app M)
  let e := (ModuleCat.extendScalarsComp φ.hom (𝟙 S : S ⟶ S).hom).hom.app
    ((relativeGlobalSections f).obj M)
  let := isIso_scalarSectionsBaseChangeMap_of_isIso (𝟙 S) f' (h ≫ f') h
    (by simp) ((Scheme.Modules.pullback g).obj M)
  have hb : IsIso (e ≫ (ModuleCat.extendScalars (𝟙 S : S ⟶ S).hom).map q ≫ t ≫ c) := by
    dsimp only [e, q, t, c]
    rw [scalarSectionsBaseChangeMap_comp]
    have aux (ψ : R ⟶ S) (hψ : ψ = φ)
        (wψ : (h ≫ g) ≫ f = (h ≫ f') ≫ Spec.map ψ) :
        IsIso (scalarSectionsBaseChangeMap ψ f (h ≫ f') (h ≫ g) wψ M) := by
      subst ψ
      exact hi
    exact aux (φ ≫ 𝟙 S) (Category.comp_id _) _
  have hleft : IsIso (e ≫ (ModuleCat.extendScalars (𝟙 S : S ⟶ S).hom).map q) := by
    exact IsIso.of_isIso_comp_right _ (t ≫ c)
  have : IsIso ((ModuleCat.extendScalars (𝟙 S : S ⟶ S).hom).map q) :=
    IsIso.of_isIso_comp_left e _
  let : (ModuleCat.extendScalars (𝟙 S : S ⟶ S).hom).IsEquivalence :=
    Functor.isEquivalence_of_iso (ModuleCat.extendScalarsId S).symm
  exact isIso_of_reflects_iso q (ModuleCat.extendScalars (𝟙 S : S ⟶ S).hom)

/-- An isomorphic source presentation preserves invertibility of canonical base change. -/
lemma isIso_scalarSectionsBaseChangeMap_comp_source_iso
    {W : Scheme.{u}} (e : W ⟶ X) [IsIso e] (fW : W ⟶ Spec R)
    (we : e ≫ f = fW ≫ Spec.map (𝟙 R)) (k : Y ⟶ W)
    (wk : k ≫ fW = f' ≫ Spec.map φ) (M : X.Modules)
    (hi : IsIso (scalarSectionsBaseChangeMap φ fW f' k wk
      ((Scheme.Modules.pullback e).obj M))) :
    IsIso (scalarSectionsBaseChangeMap φ f f' (k ≫ e)
      (by rw [Category.assoc, we, ← Category.assoc k fW, wk]; simp) M) := by
  let := isIso_scalarSectionsBaseChangeMap_of_isIso (𝟙 R) f fW e we M
  have hcomp := scalarSectionsBaseChangeMap_comp (𝟙 R) φ f fW f' e k we wk M
  have hb : IsIso ((ModuleCat.extendScalarsComp (𝟙 R : R ⟶ R).hom φ.hom).hom.app
      ((relativeGlobalSections f).obj M) ≫
      (ModuleCat.extendScalars φ.hom).map
        (scalarSectionsBaseChangeMap (𝟙 R) f fW e we M) ≫
      scalarSectionsBaseChangeMap φ fW f' k wk ((Scheme.Modules.pullback e).obj M) ≫
      (relativeGlobalSections f').map ((Scheme.Modules.pullbackComp k e).hom.app M)) := by
    infer_instance
  rw [hcomp] at hb
  have aux (ψ : R ⟶ S) (hψ : ψ = φ)
      (wψ : (k ≫ e) ≫ f = f' ≫ Spec.map ψ)
      (hiψ : IsIso (scalarSectionsBaseChangeMap ψ f f' (k ≫ e) wψ M)) :
      IsIso (scalarSectionsBaseChangeMap φ f f' (k ≫ e)
        (by rw [Category.assoc, we, ← Category.assoc k fW, wk]; simp) M) := by
    subst ψ
    exact hiψ
  exact aux (𝟙 R ≫ φ) (Category.id_comp _) _ hb

end Transport

section Affine

variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (f : X ⟶ Spec R) (f' : Y ⟶ Spec S)
  (g : Y ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)

/-- The actual scalar sections map is invertible for a Cartesian square of affine
schemes and a quasi-coherent coefficient sheaf. -/
lemma isIso_scalarSectionsBaseChangeMap_of_isPullback_affine
    (h : IsPullback g f' f (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent] :
    IsIso (scalarSectionsBaseChangeMap φ f f' g w M) := by
  let k := Y.isoSpec.inv ≫ g ≫ X.isoSpec.hom
  let fA := X.isoSpec.inv ≫ f
  let fB := Y.isoSpec.inv ≫ f'
  have wk : k ≫ fA = fB ≫ Spec.map φ := by
    simp only [k, fA, fB, Category.assoc, Iso.hom_inv_id_assoc, w]
  have hp : IsPullback k fB fA (Spec.map φ) := by
    apply h.of_iso' Y.isoSpec.symm X.isoSpec.symm (Iso.refl _) (Iso.refl _)
    · simp [k]
    · simp [fB]
    · simp [fA]
    · simp
  have : ((Scheme.Modules.pullback X.isoSpec.inv).obj M).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.inv).app M) inferInstance
  have hi := isIso_scalarSectionsBaseChangeMap_of_isPullback_spectra φ fA fB k wk hp
    ((Scheme.Modules.pullback X.isoSpec.inv).obj M)
  have hi' := isIso_scalarSectionsBaseChangeMap_comp_source_iso φ f fB
    X.isoSpec.inv fA (by simp [fA]) k wk M hi
  apply isIso_scalarSectionsBaseChangeMap_of_precomp_iso φ f f' g w Y.isoSpec.inv M
  have aux (a : Spec Γ(Y, ⊤) ⟶ X) (ha : a = Y.isoSpec.inv ≫ g)
      (wa : a ≫ f = fB ≫ Spec.map φ)
      (hia : IsIso (scalarSectionsBaseChangeMap φ f fB a wa M)) :
      IsIso (scalarSectionsBaseChangeMap φ f (Y.isoSpec.inv ≫ f') (Y.isoSpec.inv ≫ g)
        (by simp only [Category.assoc, w]) M) := by
    subst a
    exact hia
  exact aux (k ≫ X.isoSpec.inv) (by simp [k]) _ hi'

/-- Package the actual scalar sections map for any Cartesian affine square. -/
def affineCartesianScalarSectionsIso
    (h : IsPullback g f' f (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars φ.hom).obj ((relativeGlobalSections f).obj M) ≅
      (relativeGlobalSections f').obj ((Scheme.Modules.pullback g).obj M) := by
  let := isIso_scalarSectionsBaseChangeMap_of_isPullback_affine φ f f' g w h M
  exact asIso (scalarSectionsBaseChangeMap φ f f' g w M)

end Affine

end Langlands.AlgebraicGeometry.Modules.DerivedSections
