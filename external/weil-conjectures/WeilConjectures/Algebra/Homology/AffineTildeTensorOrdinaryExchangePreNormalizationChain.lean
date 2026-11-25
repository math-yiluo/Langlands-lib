/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates


public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparison
public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeRepresentative
import WeilConjectures.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde

/-! The termwise affine exchange chain map before localization.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange-prenormalization-chain). -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules

local instance (priority := 2000) chainCoordinatesCategory (Y : Scheme.{u}) :
    Category Y.Modules := SheafOfModules.instCategory (R := Y.ringCatSheaf)
local instance (priority := 2000) chainCoordinatesPreadditive (Y : Scheme.{u}) :
    Preadditive Y.Modules := SheafOfModules.instPreadditive Y.ringCatSheaf
local instance (priority := 2000) chainCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))


private theorem tilde_map_toOpen {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}
    (a : M ⟶ N) (m : M) :
    (Hom.app ((tilde.functor R).map a) ⊤) (tilde.toOpen M ⊤ m) =
      tilde.toOpen N ⊤ (a m) := by
  exact congr($(tilde.toOpen_map_app a ⊤) m)

private theorem tilde_hom_ext {R : CommRingCat.{u}}
    {M : ModuleCat.{u} R} {F : (Spec R).Modules}
    {a b : (tilde.functor R).obj M ⟶ F}
    (h : ∀ m : M, (Hom.app a ⊤) (tilde.toOpen M ⊤ m) =
      (Hom.app b ⊤) (tilde.toOpen M ⊤ m)) : a = b := by
  apply ((tilde.adjunction (R := R)).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  exact LinearMap.ext h

private theorem sigma_toOpen (A B : Type u) [CommRing A] [CommRing B]
    (ψ : B →+* A) (N : ModuleCat.{u} A) (n : N) :
    (Scheme.Modules.Hom.app ((affineTildePushforwardComparison A B ψ).hom.app N) ⊤)
      (tilde.toOpen (R := .of B) ((ModuleCat.restrictScalars ψ).obj N) ⊤ n) =
        tilde.toOpen (R := .of A) N ⊤ n := by
  let S := moduleSpecΓFunctor (R := .of A)
  let T := affinePushforwardTilde B
  let P := Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom ψ))
  let ν : ModuleCat.restrictScalars ψ ⟶
      affinePushforwardTilde A ⋙ P ⋙ moduleSpecΓFunctor (R := .of B) :=
    (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (tilde.toTildeΓNatIso (R := .of A)).hom
        (ModuleCat.restrictScalars ψ) ≫
      (Functor.associator (affinePushforwardTilde A) S (ModuleCat.restrictScalars ψ)).hom ≫
      Functor.whiskerLeft (affinePushforwardTilde A)
        (Scheme.Modules.pushforwardSpecMapCompΓIso (CommRingCat.ofHom ψ)).inv
  have h : (tilde.adjunction (R := .of B)).homEquiv _ _
      ((affineTildePushforwardComparison A B ψ).hom.app N) = ν.app N := by
    exact ((tilde.adjunction (R := .of B)).homEquiv _ _).apply_symm_apply (ν.app N)
  exact congr($h n)

private theorem baseChange_transpose
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) (F : X.Modules) :
    (Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _
        (moduleBaseChangeMap f f' g p h F) =
      (pushforward f).map
          ((Classical.choose (exists_tensorPullbackAdjunction p)).unit.app F) ≫
        (pushforwardComp p f).hom.app ((tensorPullback p).obj F) ≫
        (pushforwardCongr h).hom.app ((tensorPullback p).obj F) ≫
        (pushforwardComp f' g).inv.app ((tensorPullback p).obj F) := by
  exact ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _).apply_symm_apply _

private theorem presheaf_map_id_apply {X : Scheme.{u}} (F : X.Modules)
    (q : Γ(F, ⊤)) : F.presheaf.map (𝟙 (op ⊤)) q = q := by
  exact congr($(F.presheaf.map_id (op ⊤)) q)

attribute [local irreducible] Scheme.Modules.tensorPullback affineTildePushforwardComparison

-- The sectionwise mate calculation traverses both affine comparison interfaces.
private theorem affine_exchange_degree
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] (N : ModuleCat.{u} A)
    (φ : A →+* D) (ψ : B →+* D)
    (hw : Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (k : (ModuleCat.extendScalars (algebraMap R B)).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj N) ⟶
      (ModuleCat.restrictScalars ψ).obj ((ModuleCat.extendScalars φ).obj N))
    (hk : ∀ (b : B) (q : N), k (b ⊗ₜ[R,algebraMap R B] q) = ψ b ⊗ₜ[A,φ] q) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let p := Spec.map (CommRingCat.ofHom φ)
    let f' := Spec.map (CommRingCat.ofHom ψ)
    let θg := Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
      (CommRingCat.ofHom (algebraMap R B)))
    let θp := Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
      (CommRingCat.ofHom φ))
    (tensorPullback g).map ((affineTildePushforwardComparison A R
        (algebraMap R A)).hom.app N) ≫
      moduleBaseChangeMap f f' g p hw ((affinePushforwardTilde A).obj N) ≫
      (pushforward f').map (θp.hom.app N) =
      θg.hom.app ((ModuleCat.restrictScalars (algebraMap R A)).obj N) ≫
        (affinePushforwardTilde B).map k ≫
        (affineTildePushforwardComparison D B ψ).hom.app
          ((ModuleCat.extendScalars φ).obj N) := by
  dsimp only
  let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let ag := Classical.choose (exists_tensorPullbackAdjunction g)
  apply (ag.homEquiv _ _).injective
  rewrite [ag.homEquiv_naturality_left, ag.homEquiv_naturality_right]
  rewrite (config := { transparency := .default }) [baseChange_transpose]
  apply tilde_hom_ext (R := .of R)
  intro q
  simp only [Adjunction.homEquiv_unit, Hom.comp_app,
    pushforward_map_app, pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app, ConcreteCategory.comp_apply]
  change
    (Hom.app ((Classical.choose (exists_tensorPullback_tilde_iso
      (CommRingCat.ofHom φ))).hom.app N) ⊤)
      ((((tensorPullback (Spec.map (CommRingCat.ofHom φ))).obj
        ((affinePushforwardTilde A).obj N)).presheaf.map (𝟙 _))
      ((Hom.app ((Classical.choose (exists_tensorPullbackAdjunction
        (Spec.map (CommRingCat.ofHom φ)))).unit.app ((affinePushforwardTilde A).obj N)) ⊤)
        ((Hom.app ((affineTildePushforwardComparison A R (algebraMap R A)).hom.app N) ⊤)
          (tilde.toOpen (R := .of R) ((ModuleCat.restrictScalars (algebraMap R A)).obj N)
            ⊤ q)))) =
    (Hom.app ((affineTildePushforwardComparison D B ψ).hom.app
      ((ModuleCat.extendScalars φ).obj N)) ⊤)
      ((Hom.app ((affinePushforwardTilde B).map k) ⊤)
        ((Hom.app ((Classical.choose (exists_tensorPullback_tilde_iso
          (CommRingCat.ofHom (algebraMap R B)))).hom.app
            ((ModuleCat.restrictScalars (algebraMap R A)).obj N)) ⊤)
          ((Hom.app (ag.unit.app ((affinePushforwardTilde R).obj
            ((ModuleCat.restrictScalars (algebraMap R A)).obj N))) ⊤)
              (tilde.toOpen (R := .of R)
                ((ModuleCat.restrictScalars (algebraMap R A)).obj N) ⊤ q))))
  rewrite (config := { transparency := .default })
    [presheaf_map_id_apply ((tensorPullback (Spec.map (CommRingCat.ofHom φ))).obj
    ((affinePushforwardTilde A).obj N))]
  rewrite (config := { transparency := .default }) [sigma_toOpen A R (algebraMap R A) N q]
  rewrite (config := { transparency := .default })
    [(Classical.choose_spec (exists_tensorPullback_tilde_iso
    (CommRingCat.ofHom φ))) N q]
  rewrite (config := { transparency := .default })
    [(Classical.choose_spec (exists_tensorPullback_tilde_iso
    (CommRingCat.ofHom (algebraMap R B))))
      ((ModuleCat.restrictScalars (algebraMap R A)).obj N) q]
  rewrite (config := { transparency := .default }) [tilde_map_toOpen (R := .of B) k]
  simp only [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  rewrite (config := { transparency := .default }) [hk, map_one,
    sigma_toOpen D B ψ ((ModuleCat.extendScalars φ).obj N) _]
  rfl


variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
local instance chainPullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.tensorPullback f).Additive :=
  SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f
local instance chainPushforwardAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pushforward f).Additive := ⟨fun {_ _} {_ _} ↦ rfl⟩
local instance chainTildeAdditive (A : Type u) [CommRing A] :
    (affinePushforwardTilde A).Additive := by
  constructor
  intro M N f g
  exact tilde.map_add (R := .of A) f g

/-- The termwise pushforward comparison used in the target-map expansion.
Source: Stacks, Tag 01I9.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange-prenormalization). 
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange-prenormalization-chain)
-/
def affineTildePushforwardComplexMap
    (D B : Type u) [CommRing D] [CommRing B] (ψ : B →+* D)
    (C : CochainComplex (ModuleCat.{u} D) ℤ) :
    let P := RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom ψ)).toLRSHom.toShHom
    ((affinePushforwardTilde B).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars ψ).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (P.mapHomologicalComplex (.up ℤ)).obj
        (((affinePushforwardTilde D).mapHomologicalComplex (.up ℤ)).obj C) := by
  let σ := affineTildePushforwardComparison D B ψ
  let P := RingedSpace.moduleDirectImage
    (Spec.map (CommRingCat.ofHom ψ)).toLRSHom.toShHom
  let : P.Additive := RingedSpace.moduleDirectImage_additive _
  exact { f := fun i ↦ σ.hom.app (C.X i)
          comm' := fun i j _ ↦ (σ.hom.naturality (C.d i j)).symm }

-- The degreewise comparison includes the chosen tensor and pushforward functors.
/-- The ordinary termwise exchange chain map in affine tensor coordinates.
Source: Stacks Project, Tags 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange-prenormalization-chain).
The assertion is the pre-localization calculation: the source comparison followed by
ordinary module base change equals the coefficient map, affine pushforward comparison,
and the inverse tensor/tilde comparison. It is proved degreewise on pure tensors and
then by tensor induction and extensionality. -/
theorem affineTildeTensorOrdinaryExchange_preNormalization_chain
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (φ : A →+* D) (ψ : B →+* D)
    (hw : Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (k : (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M)) ⟶
      ((ModuleCat.restrictScalars ψ).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M))
    (hk : ∀ (i : ℤ) (b : B) (q : M.X i),
      k.f i (b ⊗ₜ[R,algebraMap R B] q) = ψ b ⊗ₜ[A,φ] q) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let p := Spec.map (CommRingCat.ofHom φ)
    let f' := Spec.map (CommRingCat.ofHom ψ)
    let C := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
    let P := ((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M
    let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) :=
      Scheme.Modules.tensorPullback p
    let F' : SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace) :=
      Scheme.Modules.pushforward f'
    let : E.Additive := chainPullbackAdditive p
    let : F'.Additive := chainPushforwardAdditive f'
    let : (affinePushforwardTilde A).Additive := chainTildeAdditive A
    let : (affinePushforwardTilde D).Additive := chainTildeAdditive D
    let : (E ⋙ F').PreservesZeroMorphisms :=
      ⟨fun _ _ ↦ by
        rw [Functor.comp_map, E.map_zero]
        exact F'.map_zero _ _⟩
    let δ := affineBaseChangeTildeComplexIso A D φ M
    let b₀ :
        (Scheme.Modules.pushforward f ⋙ Scheme.Modules.tensorPullback g) ⟶
          (E ⋙ F') :=
      { app := Scheme.Modules.moduleBaseChangeMap f f' g p hw
        naturality := fun _ _ z ↦
          Scheme.Modules.moduleBaseChangeMap_naturality f f' g p hw z }
    let b := (b₀.mapHomologicalComplex (.up ℤ)).app P
    let a := affineTildePushforwardComplexMap D B ψ C
    (affineTildeTensorOrdinarySourceIso R A B M).hom ≫ b =
      (((affinePushforwardTilde B).mapHomologicalComplex (.up ℤ)).map k) ≫ a ≫
        ((F'.mapHomologicalComplex (.up ℤ)).map δ.inv) := by
  intro f g p f' C P E F' hE hF' hTA hTD hEF δ b₀ b a
  apply HomologicalComplex.hom_ext
  intro i
  let θg := Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
    (CommRingCat.ofHom (algebraMap R B)))
  let θp := Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
    (CommRingCat.ofHom φ))
  change θg.inv.app ((ModuleCat.restrictScalars (algebraMap R A)).obj (M.X i)) ≫
      (Scheme.Modules.tensorPullback g).map
        ((affineTildePushforwardComparison A R (algebraMap R A)).hom.app (M.X i)) ≫
      Scheme.Modules.moduleBaseChangeMap f f' g p hw ((affinePushforwardTilde A).obj (M.X i)) =
    (affinePushforwardTilde B).map (k.f i) ≫
      (affineTildePushforwardComparison D B ψ).hom.app
        ((ModuleCat.extendScalars φ).obj (M.X i)) ≫
      F'.map (θp.inv.app (M.X i))
  have hd := affine_exchange_degree R A B D (M.X i) φ ψ hw (k.f i) (hk i)
  apply (cancel_epi (θg.hom.app
    ((ModuleCat.restrictScalars (algebraMap R A)).obj (M.X i)))).1
  apply (cancel_mono (F'.map (θp.hom.app (M.X i)))).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simp only [Category.assoc, ← F'.map_comp, Iso.inv_hom_id_app]
  exact hd

end AlgebraicGeometry
