import Langlands.Algebra.RenardLocalModuleCategory
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Functoriality and the Mathlib comparison for the chosen local modules -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace Langlands.Renard.ModuleLocalization.UniversalComparison

universe u v w

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- Raise sources to the common universe, using the published Mathlib functor. -/
abbrev sourceRaiseFunctor : ModuleCat.{v} R ⥤ ModuleCat.{max u v w} R :=
  ModuleCat.uliftFunctor.{max u w, v} R

@[simp] theorem sourceRaiseFunctor_obj (M : ModuleCat.{v} R) :
    (sourceRaiseFunctor.{u,v,w} (R := R)).obj M =
      raisedSource.{u,v,w} (R := R) M := rfl

@[simp] theorem sourceRaiseFunctor_map_up {M N : ModuleCat.{v} R} (f : M ⟶ N) (m : M) :
    (sourceRaiseFunctor.{u,v,w} (R := R)).map f (ULift.up m) = ULift.up (f m) := rfl

/-- The raised function is exactly `ULift.up ∘ f ∘ ULift.down`. -/
@[simp] theorem sourceRaiseFunctor_map_apply {M N : ModuleCat.{v} R} (f : M ⟶ N)
    (x : raisedSource.{u,v,w} (R := R) M) :
    (sourceRaiseFunctor.{u,v,w} (R := R)).map f x = ULift.up (f x.down) := rfl

/-- The actual localized linear map, conjugated by the two chosen lifts. -/
def chosenLocalMap {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    canonicalLocalObject.{u,v,w} S M ⟶ canonicalLocalObject.{u,v,w} S N :=
  ObjectProperty.homMk <| ModuleCat.ofHom <|
    (ULift.moduleEquiv (R := R) (M := LocalizedModule S N)).symm.toLinearMap.comp
      ((IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap S N) f.hom).comp
          (ULift.moduleEquiv (R := R) (M := LocalizedModule S M)).toLinearMap)

/-- This formula identifies the underlying map without suppressing either lift. -/
theorem chosenLocalMap_hom {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (chosenLocalMap.{u,v,w} S f).hom.hom =
      (ULift.moduleEquiv (R := R) (M := LocalizedModule S N)).symm.toLinearMap.comp
        ((IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
          (LocalizedModule.mkLinearMap S N) f.hom).comp
            (ULift.moduleEquiv (R := R) (M := LocalizedModule S M)).toLinearMap) := rfl

@[simp] theorem chosenLocalMap_mk {M N : ModuleCat.{v} R} (f : M ⟶ N) (m : M) (s : S) :
    (chosenLocalMap.{u,v,w} S f).hom (ULift.up (LocalizedModule.mk m s)) =
      ULift.up (LocalizedModule.mk (f m) s) := by
  change ULift.up (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) f.hom (LocalizedModule.mk m s)) = _
  congr 1
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk_eq_mk']
  exact IsLocalizedModule.map_mk' _ _ _ _ _ _

@[simp] theorem chosenLocalMap_id (M : ModuleCat.{v} R) :
    chosenLocalMap.{u,v,w} S (𝟙 M) = 𝟙 (canonicalLocalObject.{u,v,w} S M) := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨z⟩
  induction z using LocalizedModule.induction_on with
  | _ m s => exact chosenLocalMap_mk S (𝟙 M) m s

@[simp] theorem chosenLocalMap_comp {M N P : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ P) :
    chosenLocalMap.{u,v,w} S (f ≫ g) = chosenLocalMap S f ≫ chosenLocalMap S g := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨z⟩
  induction z using LocalizedModule.induction_on with
  | _ m s =>
    change (chosenLocalMap S (f ≫ g)).hom (ULift.up (LocalizedModule.mk m s)) =
      (chosenLocalMap S g).hom ((chosenLocalMap S f).hom (ULift.up (LocalizedModule.mk m s)))
    simp only [chosenLocalMap_mk, ModuleCat.comp_apply]

/-- Localization on exactly the previously chosen local objects. -/
def chosenLocalFunctor : ModuleCat.{v} R ⥤ LocalModuleCat.{u,max u v w} S where
  obj M := canonicalLocalObject.{u,v,w} S M
  map := chosenLocalMap S
  map_id := chosenLocalMap_id S
  map_comp := chosenLocalMap_comp S

@[simp] theorem chosenLocalFunctor_obj (M : ModuleCat.{v} R) :
    (chosenLocalFunctor.{u,v,w} S).obj M = canonicalLocalObject.{u,v,w} S M := rfl

/-- The specified canonical maps are natural for every actual module morphism. -/
def chosenLocalizationNatTrans : sourceRaiseFunctor.{u,v,w} (R := R) ⟶
    chosenLocalFunctor.{u,v,w} S ⋙ localModuleInclusion S where
  app M := canonicalModuleMap.{u,v,w} S M
  naturality {M N} f := by
    ext ⟨m⟩
    change canonicalModuleMap S N (ULift.up (f m)) =
      (chosenLocalMap S f).hom (ULift.up (LocalizedModule.mk m 1))
    simpa only [canonicalModuleMap_up, LocalizedModule.mkLinearMap_apply] using (chosenLocalMap_mk S f m 1).symm

/-- The exact specified Mathlib composite. Smallness is automatic at this universe. -/
def mathlibLocalizationFunctor : ModuleCat.{v} R ⥤ ModuleCat.{max u v w} R :=
  sourceRaiseFunctor.{u,v,w} (R := R) ⋙
    ModuleCat.localizedModuleFunctor.{max u v w} S ⋙
      ModuleCat.restrictScalars (algebraMap R (Localization S))

/-- Identity on the carrier, with the native and restricted actions compared explicitly. -/
def mathlibActionEquiv (M : ModuleCat.{v} R) :
    ((sourceRaiseFunctor.{u,v,w} (R := R)).obj M).localizedModule S ≃ₗ[R]
      (mathlibLocalizationFunctor.{u,v,w} S).obj M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change r • x = algebraMap R (Localization S) r • x
    exact (IsScalarTower.algebraMap_smul (Localization S) r x).symm

set_option backward.isDefEq.respectTransparency false in
/-- The canonical Mathlib map is linear for the actual restricted action. -/
def mathlibCanonicalMap (M : ModuleCat.{v} R) :
    (sourceRaiseFunctor.{u,v,w} (R := R)).obj M ⟶
      (mathlibLocalizationFunctor.{u,v,w} S).obj M :=
  ModuleCat.ofHom (X := (sourceRaiseFunctor.{u,v,w} (R := R)).obj M)
    (Y := (mathlibLocalizationFunctor.{u,v,w} S).obj M) <|
      (mathlibActionEquiv.{u,v,w} S M).toLinearMap.comp
    (((sourceRaiseFunctor.{u,v,w} (R := R)).obj M).localizedModuleMkLinearMap S)

/-- The function is exactly the specified Mathlib canonical function. -/
@[simp] theorem mathlibCanonicalMap_apply (M : ModuleCat.{v} R)
    (x : (sourceRaiseFunctor.{u,v,w} (R := R)).obj M) :
    mathlibCanonicalMap.{u,v,w} S M x =
      ((sourceRaiseFunctor.{u,v,w} (R := R)).obj M).localizedModuleMkLinearMap S x := rfl

set_option backward.isDefEq.respectTransparency false in
instance mathlibCanonicalMap_isLocalizedModule (M : ModuleCat.{v} R) :
    IsLocalizedModule S (mathlibCanonicalMap.{u,v,w} S M).hom := by
  exact IsLocalizedModule.of_linearEquiv S
    (((sourceRaiseFunctor.{u,v,w} (R := R)).obj M).localizedModuleMkLinearMap S)
      (mathlibActionEquiv.{u,v,w} S M)

/-- Locality concerns the restricted action on this exact composite. -/
theorem mathlibLocalizationFunctor_isSLocal (M : ModuleCat.{v} R) :
    IsSLocal S ((mathlibLocalizationFunctor.{u,v,w} S).obj M) :=
  IsLocalizedModule.map_units (mathlibCanonicalMap S M).hom

/-- Lift the same Mathlib functor through the actual full subcategory. -/
def mathlibLocalFunctor : ModuleCat.{v} R ⥤ LocalModuleCat.{u,max u v w} S :=
  (localModuleProperty S).lift (mathlibLocalizationFunctor.{u,v,w} S)
    (mathlibLocalizationFunctor_isSLocal S)

@[simp] theorem mathlibLocalFunctor_inclusion :
    mathlibLocalFunctor.{u,v,w} S ⋙ localModuleInclusion S =
      mathlibLocalizationFunctor.{u,v,w} S := rfl

@[simp] theorem mathlibLocalFunctor_obj (M : ModuleCat.{v} R) :
    (localModuleInclusion S).obj ((mathlibLocalFunctor.{u,v,w} S).obj M) =
      (mathlibLocalizationFunctor.{u,v,w} S).obj M := rfl

@[simp] theorem mathlibLocalFunctor_map {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (localModuleInclusion S).map ((mathlibLocalFunctor.{u,v,w} S).map f) =
      (mathlibLocalizationFunctor.{u,v,w} S).map f := rfl

/-- Naturality of the specified Mathlib canonical localization maps. -/
def mathlibLocalizationNatTrans : sourceRaiseFunctor.{u,v,w} (R := R) ⟶
    mathlibLocalizationFunctor.{u,v,w} S where
  app := mathlibCanonicalMap S
  naturality {M N} f := by
    ext x
    change ((sourceRaiseFunctor.obj N).localizedModuleMkLinearMap S)
        ((sourceRaiseFunctor.map f) x) =
      IsLocalizedModule.map S ((sourceRaiseFunctor.obj M).localizedModuleMkLinearMap S)
        ((sourceRaiseFunctor.obj N).localizedModuleMkLinearMap S)
          (sourceRaiseFunctor.map f).hom
            (((sourceRaiseFunctor.obj M).localizedModuleMkLinearMap S) x)
    exact (IsLocalizedModule.map_apply _ _ _ _ _).symm

/-- The published chosen canonical map really presents the raised source's localization. -/
instance canonicalModuleMap_isLocalizedModule (M : Type v) [AddCommGroup M] [Module R M] :
    IsLocalizedModule S (canonicalModuleMap.{u,v,w} S M).hom := by
  change IsLocalizedModule S
    ((ULift.moduleEquiv (R := R) (M := LocalizedModule S M)).symm.toLinearMap.comp
      ((LocalizedModule.mkLinearMap S M).comp
        (ULift.moduleEquiv (R := R) (M := M)).toLinearMap))
  infer_instance

/-- The comparison from the actual two verified localization maps. -/
def chosenMathlibLinearEquiv (M : ModuleCat.{v} R) :
    (canonicalLocalObject.{u,v,w} S M).obj ≃ₗ[R]
      (mathlibLocalizationFunctor.{u,v,w} S).obj M := by
  letI : IsLocalizedModule S (canonicalModuleMap.{u,v,w} S M).hom :=
    canonicalModuleMap_isLocalizedModule.{u,v,w} S M
  letI : IsLocalizedModule S (mathlibCanonicalMap.{u,v,w} S M).hom :=
    mathlibCanonicalMap_isLocalizedModule.{u,v,w} S M
  exact IsLocalizedModule.linearEquiv S (canonicalModuleMap.{u,v,w} S M).hom
    (mathlibCanonicalMap.{u,v,w} S M).hom

@[simp] theorem chosenMathlibLinearEquiv_canonical (M : ModuleCat.{v} R)
    (x : raisedSource.{u,v,w} (R := R) M) :
    chosenMathlibLinearEquiv.{u,v,w} S M (canonicalModuleMap S M x) =
      mathlibCanonicalMap.{u,v,w} S M x := by
  have : IsLocalizedModule S (canonicalModuleMap.{u,v,w} S M).hom :=
    canonicalModuleMap_isLocalizedModule.{u,v,w} S M
  have : IsLocalizedModule S (mathlibCanonicalMap.{u,v,w} S M).hom :=
    mathlibCanonicalMap_isLocalizedModule.{u,v,w} S M
  exact IsLocalizedModule.linearEquiv_apply S (canonicalModuleMap.{u,v,w} S M).hom
    (mathlibCanonicalMap.{u,v,w} S M).hom x

/-- The comparison is an isomorphism inside the actual full subcategory. -/
def chosenMathlibIsoComponent (M : ModuleCat.{v} R) :
    canonicalLocalObject.{u,v,w} S M ≅ (mathlibLocalFunctor.{u,v,w} S).obj M :=
  (localModuleProperty S).isoMk (chosenMathlibLinearEquiv.{u,v,w} S M).toModuleIso

/-- The comparison carries the chosen canonical arrow to Mathlib's specified arrow. -/
@[simp] theorem chosenMathlibIsoComponent_canonical (M : ModuleCat.{v} R) :
    canonicalModuleMap.{u,v,w} S M ≫
      (localModuleInclusion S).map (chosenMathlibIsoComponent.{u,v,w} S M).hom =
        mathlibCanonicalMap.{u,v,w} S M := by
  ext x
  exact chosenMathlibLinearEquiv_canonical S M x

/-- Every actual module morphism satisfies the comparison's naturality square. -/
theorem chosenMathlibIsoComponent_naturality {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (chosenLocalFunctor.{u,v,w} S).map f ≫ (chosenMathlibIsoComponent S N).hom =
      (chosenMathlibIsoComponent S M).hom ≫ (mathlibLocalFunctor S).map f := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  apply IsLocalizedModule.ext S (canonicalModuleMap.{u,v,w} S M).hom
    (mathlibLocalizationFunctor_isSLocal S N)
  apply LinearMap.ext
  intro x
  have hF := congrArg (fun k => k x) ((chosenLocalizationNatTrans.{u,v,w} S).naturality f)
  have hG := congrArg (fun k => k x) ((mathlibLocalizationNatTrans.{u,v,w} S).naturality f)
  change chosenMathlibLinearEquiv S N ((chosenLocalMap S f).hom (canonicalModuleMap S M x)) =
    (mathlibLocalizationFunctor S).map f
      (chosenMathlibLinearEquiv S M (canonicalModuleMap S M x))
  change canonicalModuleMap S N ((sourceRaiseFunctor.map f) x) =
    (chosenLocalMap S f).hom (canonicalModuleMap S M x) at hF
  rw [← hF, chosenMathlibLinearEquiv_canonical, chosenMathlibLinearEquiv_canonical]
  exact hG

/-- The actual natural isomorphism comparing the two functors and all their maps. -/
def chosenMathlibIso : chosenLocalFunctor.{u,v,w} S ≅ mathlibLocalFunctor.{u,v,w} S :=
  NatIso.ofComponents (chosenMathlibIsoComponent S) (chosenMathlibIsoComponent_naturality S)

/-- On each denominator representative the comparison is the specified Shrink/ULift map. -/
@[simp] theorem chosenMathlibIso_hom_mk (M : ModuleCat.{v} R) (m : M) (s : S) :
    ((chosenMathlibIso.{u,v,w} S).hom.app M).hom (ULift.up (LocalizedModule.mk m s)) =
      (Shrink.linearEquiv R (LocalizedModule S (ULift.{max u w} M))).symm
        (LocalizedModule.mk (ULift.up m) s) := by
  change chosenMathlibLinearEquiv S M (ULift.up (LocalizedModule.mk m s)) =
    mathlibActionEquiv S M
      ((Shrink.linearEquiv R (LocalizedModule S (ULift.{max u w} M))).symm
        (LocalizedModule.mk (ULift.up m) s))
  have hs : (s : R) • (ULift.up (LocalizedModule.mk m s) :
      (canonicalLocalObject.{u,v,w} S M).obj) = canonicalModuleMap S M (ULift.up m) := by
    change ULift.up ((s : R) • LocalizedModule.mk m s) =
      ULift.up (LocalizedModule.mk m 1)
    rw [LocalizedModule.smul'_mk, ← Submonoid.smul_def, LocalizedModule.mk_cancel]
  have hs' : (s : R) • LocalizedModule.mk (ULift.up m : ULift.{max u w} M) s =
      LocalizedModule.mkLinearMap S (ULift.{max u w} M) (ULift.up m) := by
    change (s : R) • LocalizedModule.mk (ULift.up m) s =
      LocalizedModule.mk (ULift.up m) 1
    rw [LocalizedModule.smul'_mk, ← Submonoid.smul_def, LocalizedModule.mk_cancel]
  let e := (Shrink.linearEquiv R (LocalizedModule S (ULift.{max u w} M))).symm
  apply ((isSLocal_iff_bijective S _).mp (mathlibLocalizationFunctor_isSLocal S M) s).1
  calc
    (s : R) • chosenMathlibLinearEquiv S M (ULift.up (LocalizedModule.mk m s)) =
        chosenMathlibLinearEquiv S M
          ((s : R) • (ULift.up (LocalizedModule.mk m s) :
            (canonicalLocalObject.{u,v,w} S M).obj)) :=
      ((chosenMathlibLinearEquiv S M).map_smul _ _).symm
    _ = chosenMathlibLinearEquiv S M (canonicalModuleMap S M (ULift.up m)) :=
      congrArg (chosenMathlibLinearEquiv S M) hs
    _ = mathlibCanonicalMap S M (ULift.up m) := chosenMathlibLinearEquiv_canonical S M _
    _ = mathlibActionEquiv S M (e ((s : R) • LocalizedModule.mk (ULift.up m) s)) := by
      rw [hs']
      rfl
    _ = (s : R) • mathlibActionEquiv S M (e (LocalizedModule.mk (ULift.up m) s)) := by
      rw [e.map_smul, (mathlibActionEquiv S M).map_smul]

@[simp] theorem chosenMathlibIso_canonical (M : ModuleCat.{v} R) :
    canonicalModuleMap.{u,v,w} S M ≫
      (localModuleInclusion S).map ((chosenMathlibIso.{u,v,w} S).hom.app M) =
        (mathlibLocalizationNatTrans.{u,v,w} S).app M :=
  chosenMathlibIsoComponent_canonical S M

/-- First inverse law, as an equality of actual natural transformations. -/
@[simp] theorem chosenMathlibIso_hom_inv :
    (chosenMathlibIso.{u,v,w} S).hom ≫ (chosenMathlibIso S).inv =
      𝟙 (chosenLocalFunctor.{u,v,w} S) :=
  (chosenMathlibIso S).hom_inv_id

/-- Second inverse law, as an equality of actual natural transformations. -/
@[simp] theorem chosenMathlibIso_inv_hom :
    (chosenMathlibIso.{u,v,w} S).inv ≫ (chosenMathlibIso S).hom =
      𝟙 (mathlibLocalFunctor.{u,v,w} S) :=
  (chosenMathlibIso S).inv_hom_id

end Langlands.Renard.ModuleLocalization.UniversalComparison
