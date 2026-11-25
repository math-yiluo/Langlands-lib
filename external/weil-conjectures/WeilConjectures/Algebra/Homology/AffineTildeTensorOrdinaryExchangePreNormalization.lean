/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates


public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparison
public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeRepresentative
import WeilConjectures.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
public import
  WeilConjectures.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalizationChain

/-! The derived equality before target-map expansion and direct-image reassociation. -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry

attribute [local instance 2000] chainCoordinatesCategory chainCoordinatesPreadditive
  chainCoordinatesAbelian

private theorem quotient_comp_refl_hom
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (P : CochainComplex C ℤ) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) = 𝟙 _ := by
  change (HomotopyCategory.quotient _ (.up ℤ)).map
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app P) = _
  change (HomotopyCategory.quotient E (.up ℤ)).map
    (𝟙 (((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj P)) = _
  exact (HomotopyCategory.quotient E (.up ℤ)).map_id _

private theorem quotient_comp_refl_inv
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (P : CochainComplex C ℤ) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) = 𝟙 _ := by
  change (HomotopyCategory.quotient _ (.up ℤ)).map
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app P) = _
  change (HomotopyCategory.quotient E (.up ℤ)).map
    (𝟙 (((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj P)) = _
  exact (HomotopyCategory.quotient E (.up ℤ)).map_id _
private theorem homotopyBaseChange_quotient
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive]
    (P : CochainComplex X.Modules ℤ) :
    (moduleHomotopyBaseChange f f' g p h).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        (((show Scheme.Modules.pushforward f ⋙ Scheme.Modules.tensorPullback g ⟶
            Scheme.Modules.tensorPullback p ⋙ Scheme.Modules.pushforward f' from
          { app := Scheme.Modules.moduleBaseChangeMap f f' g p h
            naturality := fun _ _ z ↦
              Scheme.Modules.moduleBaseChangeMap_naturality f f' g p h z }).mapHomologicalComplex
          (.up ℤ)).app P) := by
  dsimp only [moduleHomotopyBaseChange, NatTrans.comp_app]
  rw [quotient_comp_refl_hom, quotient_comp_refl_inv, Category.id_comp, Category.comp_id]
  rfl

private theorem derivedUnit_chain_naturality
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive]
    {K L : CochainComplex C ℤ} (z : K ⟶ L) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map z) ≫
        F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj L) =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫
        F.rightDerivedFunctor.map (DerivedCategory.Q.map z) := by
  exact F.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map z)

private theorem derivedUnit_exchange
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive]
    {T T' U : CochainComplex D ℤ} {K L : CochainComplex C ℤ}
    (s : T ⟶ T') (b : T' ⟶ (F.mapHomologicalComplex (.up ℤ)).obj L)
    (c : T ⟶ U) (d : U ⟶ (F.mapHomologicalComplex (.up ℤ)).obj K) (z : K ⟶ L)
    (h : s ≫ b = c ≫ d ≫ (F.mapHomologicalComplex (.up ℤ)).map z) :
    DerivedCategory.Q.map s ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map b) ≫
        F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj L) =
      (DerivedCategory.Q.map c ≫ DerivedCategory.Q.map d ≫
        F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≫
          F.rightDerivedFunctor.map (DerivedCategory.Q.map z) := by
  change DerivedCategory.Q.map s ≫ DerivedCategory.Q.map b ≫ _ = _
  rewrite [← Category.assoc, ← DerivedCategory.Q.map_comp, h]
  simp only [Functor.map_comp, Category.assoc]
  rewrite [derivedUnit_chain_naturality]
  rfl

private theorem ordinary_exchange_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    {T U : CochainComplex (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ}
    {K : CochainComplex (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) ℤ}
    (s : T ⟶ ((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj P))
    (c : T ⟶ U)
    (a : U ⟶ ((RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj K)
    (z : K ⟶ ((Scheme.Modules.tensorPullback p).mapHomologicalComplex (.up ℤ)).obj P)
    (hc : s ≫ (((show Scheme.Modules.pushforward f ⋙ Scheme.Modules.tensorPullback g ⟶
        Scheme.Modules.tensorPullback p ⋙ Scheme.Modules.pushforward f' from
      { app := Scheme.Modules.moduleBaseChangeMap f f' g p h
        naturality := fun _ _ v ↦
          Scheme.Modules.moduleBaseChangeMap_naturality f f' g p h v }).mapHomologicalComplex
        (.up ℤ)).app P) = c ≫ a ≫
          ((Scheme.Modules.pushforward f').mapHomologicalComplex (.up ℤ)).map z) :
    DerivedCategory.Q.map s ≫
        DerivedCategory.Qh.map ((moduleHomotopyBaseChange f f' g p h).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          (((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      (DerivedCategory.Q.map c ≫ DerivedCategory.Q.map a ≫
        (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≫
        (schemeDerivedDirectImage f').map (DerivedCategory.Q.map z) := by
  rw [homotopyBaseChange_quotient f f' g p h P]
  exact derivedUnit_exchange
    (C := SheafOfModules.{u} (moduleRings X'.toRingedSpace))
    (D := SheafOfModules.{u} (moduleRings S'.toRingedSpace))
    (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom) s _ c a z hc

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
local instance preNormTildeAdditive (A : Type u) [CommRing A] :
    (affinePushforwardTilde A).Additive := by
  constructor
  intro M N f g
  exact tilde.map_add (R := .of A) f g
local instance preNormPushforwardAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pushforward f).Additive := ⟨fun {_ _} {_ _} ↦ rfl⟩
local instance preNormPullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.tensorPullback f).Additive :=
  SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f

attribute [local irreducible] affineTildePushforwardComparison
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Scheme.Modules.tensorPullback
  affineTildeTensorOrdinarySourceIso

set_option cleanup.letToHave false in
/-- The affine exchange calculation before expanding the target coefficient map.
Source: Stacks Project, Tags 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange-prenormalization).
Proof: transpose the ordinary base-change mate under tensor pullback along f'.
The pullback/tilde comparisons send the unit to 1 tensor q, while the affine
pushforward comparison uses the same tilde unit, sections restriction and counit.
Thus both transposed maps send b tensor q to psi(b) tensor q. The hypothesis hk
identifies them on these generators. Tensor induction and complex extensionality
prove the chain-map equality. Pass it through the homotopy quotient and localization.
Naturality of the right-derived unit then moves the inverse tensor/tilde comparison
to the final direct image. This proves the displayed equation before cancellation
against the invertible derived pullback counit; no such invertibility is assumed
here. Zero complexes and zero rings use the same generator calculation. -/
private theorem affineTildeTensorOrdinaryExchange_preNormalization_private
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
      k.f i (b ⊗ₜ[R,algebraMap R B] q) = ψ b ⊗ₜ[A,φ] q)
 :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let p := Spec.map (CommRingCat.ofHom φ)
    let f' := Spec.map (CommRingCat.ofHom ψ)
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj
      (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)
    let C := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
    let P := ((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M
    let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) :=
      Scheme.Modules.tensorPullback p
    let F' : SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace) :=
      Scheme.Modules.pushforward f'
    let F := Scheme.Modules.pushforward f
    let G := Scheme.Modules.tensorPullback g
    let : E.Additive := preNormPullbackAdditive p
    let : G.Additive := preNormPullbackAdditive g
    let : F.Additive := preNormPushforwardAdditive f
    let : F'.Additive := preNormPushforwardAdditive f'
    let : (ModuleCat.extendScalars.{u, u, u} φ).Additive :=
      ModuleCat.baseDerivedTensor_extendScalars_additive _
    let : (affinePushforwardTilde A).Additive :=
      by constructor; intro M N f g; exact tilde.map_add (R := .of A) f g
    let : (affinePushforwardTilde D).Additive :=
      by constructor; intro M N f g; exact tilde.map_add (R := .of D) f g
    let : (E ⋙ F').PreservesZeroMorphisms :=
      ⟨fun _ _ ↦ by
        rw [Functor.comp_map, E.map_zero]
        exact F'.map_zero _ _⟩
    let _δ : (E.mapHomologicalComplex (.up ℤ)).obj P ≅
        ((affinePushforwardTilde D).mapHomologicalComplex (.up ℤ)).obj C :=
      (Functor.mapHomologicalComplexCompIso
        (Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
          (CommRingCat.ofHom φ))) (.up ℤ)).app M
    let b₀ :
        (Scheme.Modules.pushforward f ⋙ Scheme.Modules.tensorPullback g) ⟶
          (E ⋙ F') :=
      { app := Scheme.Modules.moduleBaseChangeMap f f' g p hw
        naturality := fun _ _ z ↦
          Scheme.Modules.moduleBaseChangeMap_naturality f f' g p hw z }
    let _b := (b₀.mapHomologicalComplex (.up ℤ)).app P
    let a := affineTildePushforwardComplexMap D B ψ C
    DerivedCategory.Q.map (affineTildeTensorOrdinarySourceIso R A B M).hom ≫
        DerivedCategory.Qh.map ((moduleHomotopyBaseChange f f' g p hw).app H) ≫
        (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          (((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).obj H) =
      (DerivedCategory.Q.map
          (((affinePushforwardTilde B).mapHomologicalComplex (.up ℤ)).map k) ≫
        DerivedCategory.Q.map a ≫
        (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((affinePushforwardTilde D).mapHomologicalComplex (.up ℤ)).obj C))) ≫
        (schemeDerivedDirectImage f').map
          (DerivedCategory.Q.map (affineBaseChangeTildeComplexIso A D φ M).inv) := by
  exact ordinary_exchange_transport
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom ψ))
    (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (Spec.map (CommRingCat.ofHom φ)) hw
    (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)
    (affineTildeTensorOrdinarySourceIso R A B M).hom
    (((affinePushforwardTilde B).mapHomologicalComplex (.up ℤ)).map k)
    (affineTildePushforwardComplexMap D B ψ
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M))
    (affineBaseChangeTildeComplexIso A D φ M).inv
    (affineTildeTensorOrdinaryExchange_preNormalization_chain R A B D M φ ψ hw k hk)

/-- Public export of the private `affineTildeTensorOrdinaryExchange_preNormalization_private`
(used by `import all` importers; linter.privateModule). -/
alias affineTildeTensorOrdinaryExchange_preNormalization :=
  affineTildeTensorOrdinaryExchange_preNormalization_private

end AlgebraicGeometry
