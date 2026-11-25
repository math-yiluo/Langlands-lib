/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import WeilConjectures.Algebra.Homology.AffineBaseChangeIntoPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Explicit coordinates for affine base-change cohomology

Source: Stacks Project, Tags 0DJ8, 06Y6 and 01I9.
(blueprint: def-pc-affine-base-change-tilde-coordinates). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

/-- Exact tilde preserves zero morphisms. Source: Stacks, Tag 01I9.
(blueprint: def-pc-affine-base-change-tilde-coordinates). -/
@[instance] theorem affineBaseChangeTilde_preservesZero (A : Type u) [CommRing A] :
    (@id (ModuleCat.{u} A ⥤ SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace))
        (tilde.functor (.of A))).PreservesZeroMorphisms :=
  ⟨fun _ _ ↦ tilde.map_zero⟩

/-- Exact tilde commutes with cohomology. Source: Stacks, Tag 01I9.
(blueprint: def-pc-affine-base-change-tilde-coordinates).
Proof: tilde is left adjoint to global sections, so preserves cokernels. Its maps
on sections are maps of localizations, which preserve injectivity. Thus it preserves
monomorphisms and cokernels, and consequently homology. -/
theorem tilde_preservesHomology (A : Type u) [CommRing A] :
    (@id (ModuleCat.{u} A ⥤ SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace))
        (tilde.functor (.of A))).PreservesHomology := by
  let T : ModuleCat.{u} A ⥤ SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) := tilde.functor (.of A)
  let : T.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of A) f g
  have adj : T ⊣ moduleSpecΓFunctor (R := .of A) := tilde.adjunction
  let : T.IsLeftAdjoint := adj.isLeftAdjoint
  let : PreservesFiniteColimits T := inferInstance
  let : T.PreservesMonomorphisms := ⟨by
    intro M N f hf
    let : Mono f := hf
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U s t h
    apply Subtype.ext
    funext x
    apply IsLocalizedModule.map_injective x.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl N)
      f.hom ((ModuleCat.mono_iff_injective f).mp inferInstance)
    exact congrArg (fun z ↦ z.val x) h⟩
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels T

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The canonical target coordinates, obtained from ordinary tensor pullback and its
universal derived counit. Source: Stacks, Tags 01I9 and 0DJ8.
(blueprint: def-pc-affine-base-change-tilde-coordinates).
This is an actual composite of isomorphisms: exact tilde commutes with homology;
the termwise pullback comparison identifies the extended complex; the inverse
counit and the supplied representative isomorphism identify its derived object. -/
def affineBaseChangeTildeCohomologyIso
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M))))
    (i : ℤ) :
    (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M).homology i ≅
      (moduleSpecΓFunctor (R := .of A')).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i).obj
            ((derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj K)) := by
  let TA : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) := tilde.functor (.of A)
  let TB : ModuleCat.{u} A' ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace) := tilde.functor (.of A')
  let : TA.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of A) f g
  let : TB.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of A') f g
  let : TA.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let : TB.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let : TB.PreservesHomology := tilde_preservesHomology A'
  let f := Spec.map (CommRingCat.ofHom φ)
  let : IsIso ((SingleComplexBaseChange.counit f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((TA.mapHomologicalComplex (.up ℤ)).obj M))) := hc
  let θ := Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
    (CommRingCat.ofHom φ))
  let P := (TA.mapHomologicalComplex (.up ℤ)).obj M
  let C := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
  let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace) :=
    Scheme.Modules.tensorPullback f
  let : E.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f
  let θ' : TA ⋙ E ≅ ModuleCat.extendScalars φ ⋙ TB := θ
  let δ : (E.mapHomologicalComplex (.up ℤ)).obj P ≅
      (TB.mapHomologicalComplex (.up ℤ)).obj C :=
    (Functor.mapHomologicalComplexCompIso θ' (.up ℤ)).app M
  let eC : DerivedCategory.Q.obj ((TB.mapHomologicalComplex (.up ℤ)).obj C) ≅
      (derivedPullback f).obj K :=
    (DerivedCategory.Q.mapIso δ).symm ≪≫
      ((DerivedCategory.quotientCompQhIso _).app
        ((E.mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
      DerivedCategory.Qh.mapIso ((E.mapHomotopyCategoryFactors (.up ℤ)).symm.app P) ≪≫
      (asIso ((SingleComplexBaseChange.counit f).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P))).symm ≪≫
      (derivedPullback f).mapIso ((DerivedCategory.quotientCompQhIso _).app P) ≪≫
      (derivedPullback f).mapIso e
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i
  exact tilde.isoTop (R := .of A') (C.homology i) ≪≫
    (moduleSpecΓFunctor (R := .of A')).mapIso
      (((C.sc i).mapHomologyIso TB).symm ≪≫
        ((DerivedCategory.homologyFunctorFactors _ i).app
          ((TB.mapHomologicalComplex (.up ℤ)).obj C)).symm ≪≫ H.mapIso eC)

/-- Extend the tensor-algebra source cohomology to the actual upper-left ring.
Source: Stacks, Tag 0DJ8, displayed affine cohomology map.
(blueprint: def-pc-affine-base-change-tilde-coordinates). -/
def affineBaseChangeTildeModule
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D) (i : ℤ) : ModuleCat.{u} D :=
  (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (m.cohomology i)

/-- The actual module arrow is the tensor comparison followed by canonical target
coordinates. Source: Stacks, Tag 0DJ8, affine proof.
(blueprint: def-pc-affine-base-change-tilde-coordinates).
The equality hφ transports the extended complex along the specified ring map;
no module is chosen from a mere existence theorem. -/
def affineBaseChangeTildeModuleMap
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D)
    (φ : A →+* D)
    (hφ : (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B)) = φ)
    (i : ℤ) (V : ModuleCat.{u} D)
    (b : (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M).homology i ≅ V)
    : affineBaseChangeTildeModule R A B D M m i ⟶ V :=
  m.localizedComparison i ≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.up ℤ) i).map
      (eqToHom (by rw [hφ] :
        ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
          (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj M =
        ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) ≫ b.hom

end AlgebraicGeometry
