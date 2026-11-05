import Langlands.Algebra.RenardLocalModuleCategory
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Functorial chosen module localization and comparison with Mathlib -/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Renard.ModuleLocalization

universe u v w

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- The specified source functor into the common carrier universe. -/
abbrev sourceRaisingFunctor : ModuleCat.{v} R ⥤ ModuleCat.{max u v w} R :=
  ModuleCat.uliftFunctor.{max u w, v} R

theorem sourceRaisingFunctor_obj (M : ModuleCat.{v} R) :
    (sourceRaisingFunctor.{u, v, w} (R := R)).obj M =
      raisedSource.{u, v, w} (R := R) M :=
  rfl

@[simp] theorem sourceRaisingFunctor_map_apply {M N : ModuleCat.{v} R} (f : M ⟶ N)
    (x : (sourceRaisingFunctor.{u, v, w} (R := R)).obj M) :
    (sourceRaisingFunctor.{u, v, w} (R := R)).map f x = ULift.up (f x.down) :=
  rfl

@[simp] theorem sourceRaisingFunctor_map_up {M N : ModuleCat.{v} R} (f : M ⟶ N)
    (m : M) :
    (sourceRaisingFunctor.{u, v, w} (R := R)).map f (ULift.up m) = ULift.up (f m) :=
  rfl

/-- The actual localized map, conjugated by the published lifts. -/
def chosenLocalMap {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    canonicalLocalObject.{u, v, w} S M ⟶ canonicalLocalObject.{u, v, w} S N :=
  ObjectProperty.homMk <| ModuleCat.ofHom <|
    (ULift.moduleEquiv (R := R) (M := LocalizedModule S N)).symm.toLinearMap.comp
      ((IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap S N) f.hom).comp
          (ULift.moduleEquiv (R := R) (M := LocalizedModule S M)).toLinearMap)

theorem chosenLocalMap_hom {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (chosenLocalMap.{u, v, w} S f).hom.hom =
      (ULift.moduleEquiv (R := R) (M := LocalizedModule S N)).symm.toLinearMap.comp
        ((IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
          (LocalizedModule.mkLinearMap S N) f.hom).comp
            (ULift.moduleEquiv (R := R) (M := LocalizedModule S M)).toLinearMap) :=
  rfl

@[simp] theorem chosenLocalMap_up_mk {M N : ModuleCat.{v} R} (f : M ⟶ N)
    (m : M) (s : S) :
    (chosenLocalMap.{u, v, w} S f).hom (ULift.up (LocalizedModule.mk m s)) =
      ULift.up (LocalizedModule.mk (f m) s) := by
  exact congrArg ULift.up (IsLocalizedModule.map_LocalizedModules S f.hom m s)

@[simp] theorem chosenLocalMap_id (M : ModuleCat.{v} R) :
    chosenLocalMap.{u, v, w} S (𝟙 M) = 𝟙 (canonicalLocalObject.{u, v, w} S M) := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases x with ⟨z⟩
  induction z using LocalizedModule.induction_on with
  | _ m s => exact chosenLocalMap_up_mk S (𝟙 M) m s

@[simp] theorem chosenLocalMap_comp {M N P : ModuleCat.{v} R}
    (f : M ⟶ N) (g : N ⟶ P) :
    chosenLocalMap.{u, v, w} S (f ≫ g) =
      chosenLocalMap.{u, v, w} S f ≫ chosenLocalMap.{u, v, w} S g := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases x with ⟨z⟩
  induction z using LocalizedModule.induction_on with
  | _ m s =>
    change (chosenLocalMap.{u, v, w} S (f ≫ g)).hom
        (ULift.up (LocalizedModule.mk m s)) =
      (chosenLocalMap.{u, v, w} S g).hom
        ((chosenLocalMap.{u, v, w} S f).hom (ULift.up (LocalizedModule.mk m s)))
    simp only [chosenLocalMap_up_mk, ModuleCat.comp_apply]
    rfl

/-- Localization with exactly the previously published chosen objects. -/
def chosenLocalFunctor : ModuleCat.{v} R ⥤ LocalModuleCat.{u, max u v w} S where
  obj M := canonicalLocalObject.{u, v, w} S M
  map f := chosenLocalMap.{u, v, w} S f
  map_id := chosenLocalMap_id S
  map_comp := chosenLocalMap_comp S

theorem chosenLocalFunctor_obj (M : ModuleCat.{v} R) :
    (chosenLocalFunctor.{u, v, w} S).obj M = canonicalLocalObject.{u, v, w} S M :=
  rfl

theorem chosenLocalFunctor_map {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (chosenLocalFunctor.{u, v, w} S).map f = chosenLocalMap.{u, v, w} S f :=
  rfl

/-- The published canonical arrows are natural for actual module morphisms. -/
def chosenLocalizationUnit :
    sourceRaisingFunctor.{u, v, w} (R := R) ⟶
      chosenLocalFunctor.{u, v, w} S ⋙ localModuleInclusion.{u, max u v w} S where
  app M := canonicalModuleMap.{u, v, w} S M
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases x with ⟨m⟩
    change ULift.up (LocalizedModule.mk (f m) 1) =
      (chosenLocalMap.{u, v, w} S f).hom (ULift.up (LocalizedModule.mk m 1))
    exact (chosenLocalMap_up_mk S f m 1).symm

theorem chosenLocalizationUnit_app (M : ModuleCat.{v} R) :
    (chosenLocalizationUnit.{u, v, w} S).app M = canonicalModuleMap.{u, v, w} S M :=
  rfl

theorem chosenLocalizationUnit_naturality {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (sourceRaisingFunctor.{u, v, w} (R := R)).map f ≫
        canonicalModuleMap.{u, v, w} S N =
      canonicalModuleMap.{u, v, w} S M ≫ (chosenLocalMap.{u, v, w} S f).hom :=
  (chosenLocalizationUnit.{u, v, w} S).naturality f

/-- Identity on the Shrink carrier, with native and restricted actions explicit. -/
def mathlibActionEquiv (M : ModuleCat.{max u v} R) :
    M.localizedModule S ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R (Localization S))).obj
        (M.localizedModule S) where
  toFun z := z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r z := by
    change r • z = (algebraMap R (Localization S) r) • z
    exact (IsScalarTower.algebraMap_smul (Localization S) r z).symm

@[simp] theorem mathlibActionEquiv_apply (M : ModuleCat.{max u v} R)
    (z : M.localizedModule S) :
    mathlibActionEquiv.{u, v} S M z = z :=
  rfl

/-- The exact specified composite, including its actual restricted action. -/
abbrev mathlibLocalizationFunctor :
    ModuleCat.{v} R ⥤ ModuleCat.{max u v w} R :=
  sourceRaisingFunctor.{u, v, w} (R := R) ⋙
    ModuleCat.localizedModuleFunctor.{max u v w} S ⋙
      ModuleCat.restrictScalars (algebraMap R (Localization S))

/-- Mathlib's canonical map, made linear for the restricted action. -/
def mathlibCanonicalMap (M : ModuleCat.{v} R) :
    (sourceRaisingFunctor.{u, v, w} (R := R)).obj M ⟶
      (mathlibLocalizationFunctor.{u, v, w} S).obj M :=
  ModuleCat.ofHom (Y := (mathlibLocalizationFunctor.{u, v, w} S).obj M) <|
    (mathlibActionEquiv.{u, max v w} S
      ((sourceRaisingFunctor.{u, v, w} (R := R)).obj M)).toLinearMap.comp
        (((sourceRaisingFunctor.{u, v, w} (R := R)).obj M).localizedModuleMkLinearMap S)

@[simp] theorem mathlibCanonicalMap_apply (M : ModuleCat.{v} R)
    (m : (sourceRaisingFunctor.{u, v, w} (R := R)).obj M) :
    mathlibCanonicalMap.{u, v, w} S M m =
      ((sourceRaisingFunctor.{u, v, w} (R := R)).obj M).localizedModuleMkLinearMap S m :=
  rfl

instance mathlibCanonicalMap_isLocalizedModule (M : ModuleCat.{v} R) :
    IsLocalizedModule S (mathlibCanonicalMap.{u, v, w} S M).hom :=
  IsLocalizedModule.of_linearEquiv S _ (mathlibActionEquiv.{u, max v w} S _)

theorem mathlibLocalizationFunctor_isSLocal (M : ModuleCat.{v} R) :
    IsSLocal S ((mathlibLocalizationFunctor.{u, v, w} S).obj M) :=
  IsLocalizedModule.map_units (mathlibCanonicalMap.{u, v, w} S M).hom

/-- The same Mathlib functor lifted to the actual full subcategory. -/
def mathlibLocalFunctor : ModuleCat.{v} R ⥤ LocalModuleCat.{u, max u v w} S :=
  (localModuleProperty.{u, max u v w} S).lift
    (mathlibLocalizationFunctor.{u, v, w} S) (mathlibLocalizationFunctor_isSLocal S)

theorem mathlibLocalFunctor_obj (M : ModuleCat.{v} R) :
    ((mathlibLocalFunctor.{u, v, w} S).obj M).obj =
      (mathlibLocalizationFunctor.{u, v, w} S).obj M :=
  rfl

theorem mathlibLocalFunctor_map {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    ((mathlibLocalFunctor.{u, v, w} S).map f).hom =
      (mathlibLocalizationFunctor.{u, v, w} S).map f :=
  rfl

theorem mathlibLocalFunctor_comp_inclusion :
    mathlibLocalFunctor.{u, v, w} S ⋙ localModuleInclusion.{u, max u v w} S =
      mathlibLocalizationFunctor.{u, v, w} S :=
  rfl

/-- Naturality of the specified canonical Mathlib maps. -/
def mathlibLocalizationUnit :
    sourceRaisingFunctor.{u, v, w} (R := R) ⟶
      mathlibLocalizationFunctor.{u, v, w} S where
  app M := mathlibCanonicalMap.{u, v, w} S M
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change ((sourceRaisingFunctor.{u, v, w} (R := R)).obj N).localizedModuleMkLinearMap S
        (((sourceRaisingFunctor.{u, v, w} (R := R)).map f) m) =
      IsLocalizedModule.map S
        (((sourceRaisingFunctor.{u, v, w} (R := R)).obj M).localizedModuleMkLinearMap S)
        (((sourceRaisingFunctor.{u, v, w} (R := R)).obj N).localizedModuleMkLinearMap S)
        (((sourceRaisingFunctor.{u, v, w} (R := R)).map f).hom)
        (((sourceRaisingFunctor.{u, v, w} (R := R)).obj M).localizedModuleMkLinearMap S m)
    exact (IsLocalizedModule.map_apply S _ _ _ m).symm

theorem mathlibLocalizationUnit_app (M : ModuleCat.{v} R) :
    (mathlibLocalizationUnit.{u, v, w} S).app M = mathlibCanonicalMap.{u, v, w} S M :=
  rfl

theorem mathlibLocalizationUnit_naturality {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (sourceRaisingFunctor.{u, v, w} (R := R)).map f ≫
        mathlibCanonicalMap.{u, v, w} S N =
      mathlibCanonicalMap.{u, v, w} S M ≫
        (mathlibLocalizationFunctor.{u, v, w} S).map f :=
  (mathlibLocalizationUnit.{u, v, w} S).naturality f

instance canonicalModuleMap_isLocalizedModule (M : ModuleCat.{v} R) :
    IsLocalizedModule S (canonicalModuleMap.{u, v, w} S M).hom := by
  change IsLocalizedModule S
    ((ULift.moduleEquiv (R := R) (M := LocalizedModule S M) :
        ULift.{w} (LocalizedModule S M) ≃ₗ[R] LocalizedModule S M).symm.toLinearMap.comp
      ((LocalizedModule.mkLinearMap S M).comp
        (ULift.moduleEquiv (R := R) (M := M) :
          ULift.{max u w} M ≃ₗ[R] M).toLinearMap))
  let := IsLocalizedModule.of_linearEquiv_right S
    (LocalizedModule.mkLinearMap S M)
    (ULift.moduleEquiv (R := R) (M := M) :
      ULift.{max u w} M ≃ₗ[R] M)
  exact IsLocalizedModule.of_linearEquiv S _
    (ULift.moduleEquiv (R := R) (M := LocalizedModule S M)).symm

/-- Localizing the actual equivalence from the original source to its lift. -/
def localizationRaisingEquiv (M : ModuleCat.{v} R) :
    LocalizedModule S M ≃ₗ[R]
      LocalizedModule S ((sourceRaisingFunctor.{u, v, w} (R := R)).obj M) :=
  (IsLocalizedModule.mapEquiv S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S
      ((sourceRaisingFunctor.{u, v, w} (R := R)).obj M))
    (Localization S) (ULift.moduleEquiv (R := R) (M := M)).symm).restrictScalars R

@[simp] theorem localizationRaisingEquiv_mk (M : ModuleCat.{v} R) (m : M) (s : S) :
    localizationRaisingEquiv.{u, v, w} S M (LocalizedModule.mk m s) =
      LocalizedModule.mk (ULift.up m) s := by
  exact IsLocalizedModule.map_LocalizedModules S
    (ULift.moduleEquiv (R := R) (M := M)).symm.toLinearMap m s

/-- The explicit comparison, retaining the actual restricted target action. -/
def chosenMathlibLinearEquiv (M : ModuleCat.{v} R) :
    (canonicalLocalObject.{u, v, w} S M).obj ≃ₗ[R]
      (mathlibLocalizationFunctor.{u, v, w} S).obj M :=
  (ULift.moduleEquiv (R := R) (M := LocalizedModule S M)).trans
    ((localizationRaisingEquiv.{u, v, w} S M).trans
      ((Shrink.linearEquiv R
        (LocalizedModule S ((sourceRaisingFunctor.{u, v, w} (R := R)).obj M))).symm.trans
          (mathlibActionEquiv.{u, max v w} S
            ((sourceRaisingFunctor.{u, v, w} (R := R)).obj M))))

@[simp] theorem chosenMathlibLinearEquiv_up_mk (M : ModuleCat.{v} R)
    (m : M) (s : S) :
    chosenMathlibLinearEquiv.{u, v, w} S M (ULift.up (LocalizedModule.mk m s)) =
      (Shrink.linearEquiv R
        (LocalizedModule S (ULift.{max u w} M))).symm
          (LocalizedModule.mk (ULift.up m) s) := by
  change (Shrink.linearEquiv R
      (LocalizedModule S ((sourceRaisingFunctor.{u, v, w} (R := R)).obj M))).symm
        (localizationRaisingEquiv.{u, v, w} S M (LocalizedModule.mk m s)) = _
  rw [localizationRaisingEquiv_mk]
  rfl

/-- Compatibility with the specified canonical Mathlib map. -/
theorem chosenMathlibLinearEquiv_comp (M : ModuleCat.{v} R) :
    canonicalModuleMap.{u, v, w} S M ≫
      ModuleCat.ofHom (chosenMathlibLinearEquiv.{u, v, w} S M).toLinearMap =
        mathlibCanonicalMap.{u, v, w} S M := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases x with ⟨m⟩
  exact chosenMathlibLinearEquiv_up_mk S M m 1

/-- The chosen localization and the specified Mathlib lift are naturally isomorphic. -/
def chosenMathlibIso :
    chosenLocalFunctor.{u, v, w} S ≅ mathlibLocalFunctor.{u, v, w} S :=
  NatIso.ofComponents
    (fun M => (localModuleProperty.{u, max u v w} S).isoMk
      (chosenMathlibLinearEquiv.{u, v, w} S M).toModuleIso)
    (by
      intro M N f
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply IsLocalizedModule.ext S (canonicalModuleMap.{u, v, w} S M).hom
        (mathlibLocalizationFunctor_isSLocal S N)
      apply LinearMap.ext
      intro x
      rcases x with ⟨m⟩
      change chosenMathlibLinearEquiv.{u, v, w} S N
          ((chosenLocalMap.{u, v, w} S f).hom (ULift.up (LocalizedModule.mk m 1))) =
        (mathlibLocalizationFunctor.{u, v, w} S).map f
          (chosenMathlibLinearEquiv.{u, v, w} S M (ULift.up (LocalizedModule.mk m 1)))
      rw [chosenLocalMap_up_mk, chosenMathlibLinearEquiv_up_mk,
        chosenMathlibLinearEquiv_up_mk]
      exact congrArg
        (fun h : (sourceRaisingFunctor.{u, v, w} (R := R)).obj M ⟶
            (mathlibLocalizationFunctor.{u, v, w} S).obj N => h (ULift.up m))
        ((mathlibLocalizationUnit.{u, v, w} S).naturality f))

@[simp] theorem chosenMathlibIso_hom_up_mk (M : ModuleCat.{v} R) (m : M) (s : S) :
    ((chosenMathlibIso.{u, v, w} S).hom.app M).hom
        (ULift.up (LocalizedModule.mk m s)) =
      (Shrink.linearEquiv R
        (LocalizedModule S (ULift.{max u w} M))).symm
          (LocalizedModule.mk (ULift.up m) s) :=
  chosenMathlibLinearEquiv_up_mk S M m s

theorem chosenMathlibIso_canonical (M : ModuleCat.{v} R) :
    canonicalModuleMap.{u, v, w} S M ≫
      (localModuleInclusion.{u, max u v w} S).map
        ((chosenMathlibIso.{u, v, w} S).hom.app M) =
      (mathlibLocalizationUnit.{u, v, w} S).app M :=
  chosenMathlibLinearEquiv_comp S M

theorem chosenMathlibIso_naturality {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (chosenLocalFunctor.{u, v, w} S).map f ≫
        (chosenMathlibIso.{u, v, w} S).hom.app N =
      (chosenMathlibIso.{u, v, w} S).hom.app M ≫
        (mathlibLocalFunctor.{u, v, w} S).map f :=
  (chosenMathlibIso.{u, v, w} S).hom.naturality f

@[simp] theorem chosenMathlibIso_hom_inv (M : ModuleCat.{v} R) :
    (chosenMathlibIso.{u, v, w} S).hom.app M ≫
      (chosenMathlibIso.{u, v, w} S).inv.app M =
        𝟙 ((chosenLocalFunctor.{u, v, w} S).obj M) :=
  (chosenMathlibIso.{u, v, w} S).hom_inv_id_app M

@[simp] theorem chosenMathlibIso_inv_hom (M : ModuleCat.{v} R) :
    (chosenMathlibIso.{u, v, w} S).inv.app M ≫
      (chosenMathlibIso.{u, v, w} S).hom.app M =
        𝟙 ((mathlibLocalFunctor.{u, v, w} S).obj M) :=
  (chosenMathlibIso.{u, v, w} S).inv_hom_id_app M

end Langlands.Renard.ModuleLocalization
