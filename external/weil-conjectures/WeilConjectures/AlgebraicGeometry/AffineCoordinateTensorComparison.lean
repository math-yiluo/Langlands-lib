/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.AlgebraicGeometry.AffineCoordinateModuleModels
public import WeilConjectures.AlgebraicGeometry.PerfectHomCochainCounit
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition

/-! # Canonical underived comparison in affine coordinates
Source: Stacks Project, Tags 01I9 and 08DW.
(blueprint: lem-pc-affine-coordinate-tensor-comparison). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- Global sections in a supplied affine coordinate chart. 
(blueprint: lem-pc-affine-coordinate-tensor-comparison)
-/
noncomputable abbrev affineCoordinateGamma (a : AffineComparisonCoordinate.{u, w}) :=
  Scheme.Modules.pushforward a.σ.inv ⋙ moduleSpecΓFunctor (R := a.A)

/-- The concrete chart model is left adjoint to its coordinate global sections. 
(blueprint: lem-pc-affine-coordinate-tensor-comparison)
-/
noncomputable def affineCoordinateAdjunction (a : AffineComparisonCoordinate.{u, w}) :
    affineCoordinateModules a ⊣ affineCoordinateGamma a :=
  tilde.adjunction.comp (affineCoordinateModuleEquivalence a.σ).toAdjunction

/-- The right-adjoint comparison of a commuting affine square. 
(blueprint: lem-pc-affine-coordinate-tensor-comparison)
-/
noncomputable def affineCoordinateGammaComparison
    (a b : AffineComparisonCoordinate.{u, w}) (φ : a.A →+* b.A)
    (p : b.X ⟶ a.X)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom) :
    Scheme.Modules.pushforward p ⋙ affineCoordinateGamma a ≅
      affineCoordinateGamma b ⋙ ModuleCat.restrictScalars φ := by
  have h : p ≫ a.σ.inv = b.σ.inv ≫ Spec.map (CommRingCat.ofHom φ) := by
    apply (cancel_epi b.σ.hom).mp
    simpa only [← Category.assoc, Iso.hom_inv_id_assoc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] using congrArg (fun t ↦ t ≫ a.σ.inv) hp
  exact (Functor.associator (Scheme.Modules.pushforward p)
    (Scheme.Modules.pushforward a.σ.inv) (moduleSpecΓFunctor (R := a.A))).symm ≪≫
    Functor.isoWhiskerRight
      (Scheme.Modules.pushforwardComp p a.σ.inv ≪≫
        Scheme.Modules.pushforwardCongr h ≪≫
        (Scheme.Modules.pushforwardComp b.σ.inv (Spec.map (CommRingCat.ofHom φ))).symm)
      (moduleSpecΓFunctor (R := a.A)) ≪≫
    Functor.associator (Scheme.Modules.pushforward b.σ.inv)
      (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ)))
      (moduleSpecΓFunctor (R := a.A)) ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pushforward b.σ.inv)
      (Scheme.Modules.pushforwardSpecMapCompΓIso (CommRingCat.ofHom φ)) ≪≫
    (Functor.associator (Scheme.Modules.pushforward b.σ.inv)
      (moduleSpecΓFunctor (R := b.A)) (ModuleCat.restrictScalars φ)).symm

/-- The scalar-extension comparison is the mate of the global-sections comparison. -/
@[irreducible] noncomputable def affineCoordinateTensorComparison
    (a b : AffineComparisonCoordinate.{u, w}) (φ : a.A →+* b.A)
    (p : b.X ⟶ a.X)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom) :
    affineCoordinateModules a ⋙ Scheme.Modules.tensorPullback p ≅
      ModuleCat.extendScalars φ ⋙ affineCoordinateModules b :=
  (conjugateIsoEquiv
    ((ModuleCat.extendRestrictScalarsAdj φ).comp (affineCoordinateAdjunction b))
    ((affineCoordinateAdjunction a).comp
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p)))).symm
    (affineCoordinateGammaComparison a b φ p hp).symm

/-- The right comparisons compose by restriction of scalars.
Source: Stacks Project, Tags 01I9 and 08DW.
(blueprint: lem-pc-affine-coordinate-tensor-comparison).
Proof: every factor acts as the identity on the underlying global section.
The equalities of maps only transport inverse-image opens; at the whole space
these are the same open. Restriction of scalars also acts as the identity. -/
theorem affineCoordinateGammaComparison_comp
    (a b c : AffineComparisonCoordinate.{u, w})
    (φ : a.A →+* b.A) (ψ : b.A →+* c.A) (p : b.X ⟶ a.X) (q : c.X ⟶ b.X)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
    (hq : c.σ.hom ≫ q = Spec.map (CommRingCat.ofHom ψ) ≫ b.σ.hom)
    (hs : c.σ.hom ≫ (q ≫ p) = Spec.map (CommRingCat.ofHom (ψ.comp φ)) ≫ a.σ.hom) :
    affineCoordinateGammaComparison a c (ψ.comp φ) (q ≫ p) hs =
      Functor.isoWhiskerRight (Scheme.Modules.pushforwardComp q p).symm
        (affineCoordinateGamma a) ≪≫
      Functor.associator (Scheme.Modules.pushforward q) (Scheme.Modules.pushforward p)
        (affineCoordinateGamma a) ≪≫
      Functor.isoWhiskerLeft (Scheme.Modules.pushforward q)
        (affineCoordinateGammaComparison a b φ p hp) ≪≫
      (Functor.associator (Scheme.Modules.pushforward q) (affineCoordinateGamma b)
        (ModuleCat.restrictScalars φ)).symm ≪≫
      Functor.isoWhiskerRight (affineCoordinateGammaComparison b c ψ q hq)
        (ModuleCat.restrictScalars φ) ≪≫
      Functor.associator (affineCoordinateGamma c) (ModuleCat.restrictScalars ψ)
        (ModuleCat.restrictScalars φ) ≪≫
      Functor.isoWhiskerLeft (affineCoordinateGamma c)
        (ModuleCat.restrictScalarsComp φ ψ).symm := by
  ext F m
  change F.presheaf.map (𝟙 _) m =
    F.presheaf.map (𝟙 _) (F.presheaf.map (𝟙 _) m)
  simp

/-- The underived affine comparisons respect the fixed scalar and pullback mates.
Source: Stacks Project, Tags 01I9 and 08DW; uniqueness and pasting of adjoints.
(blueprint: lem-pc-affine-coordinate-tensor-comparison).
Proof: the global-sections comparisons compose, since they preserve the underlying
section. Apply the proved pasting theorem for adjunction squares. The scalar and
tensor composition maps are exactly the mates of restriction and pushforward
composition, respectively. Evaluate the natural-isomorphism identity at M. -/
theorem affineCoordinateTensorComparison_comp
    (a b c : AffineComparisonCoordinate.{u, w})
    (φ : a.A →+* b.A) (ψ : b.A →+* c.A) (p : b.X ⟶ a.X) (q : c.X ⟶ b.X)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
    (hq : c.σ.hom ≫ q = Spec.map (CommRingCat.ofHom ψ) ≫ b.σ.hom)
    (hs : c.σ.hom ≫ (q ≫ p) = Spec.map (CommRingCat.ofHom (ψ.comp φ)) ≫ a.σ.hom)
    (M : ModuleCat.{u} a.A) :
    (Scheme.Modules.tensorPullback q).mapIso
        ((affineCoordinateTensorComparison a b φ p hp).app M) ≪≫
        (affineCoordinateTensorComparison b c ψ q hq).app
          ((ModuleCat.extendScalars φ).obj M) =
      (perfectHomTensorComp q p).app ((affineCoordinateModules a).obj M) ≪≫
        (affineCoordinateTensorComparison a c (ψ.comp φ) (q ≫ p) hs).app M ≪≫
        (affineCoordinateModules c).mapIso ((ModuleCat.extendScalarsComp φ ψ).app M) := by
  have h := adjunctionSquareComposition
    (affineCoordinateAdjunction a) (affineCoordinateAdjunction b)
    (affineCoordinateAdjunction c)
    (ModuleCat.extendRestrictScalarsAdj φ) (ModuleCat.extendRestrictScalarsAdj ψ)
    (ModuleCat.extendRestrictScalarsAdj (ψ.comp φ))
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p))
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q))
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (q ≫ p)))
    (affineCoordinateGammaComparison a b φ p hp)
    (affineCoordinateGammaComparison b c ψ q hq)
    (affineCoordinateGammaComparison a c (ψ.comp φ) (q ≫ p) hs)
    (ModuleCat.restrictScalarsComp φ ψ) (Scheme.Modules.pushforwardComp q p)
    (affineCoordinateTensorComparison a b φ p hp)
    (affineCoordinateTensorComparison b c ψ q hq)
    (affineCoordinateTensorComparison a c (ψ.comp φ) (q ≫ p) hs)
    (ModuleCat.extendScalarsComp φ ψ) (perfectHomTensorComp q p)
    (by unfold affineCoordinateTensorComparison; exact Equiv.apply_symm_apply _ _)
    (by unfold affineCoordinateTensorComparison; exact Equiv.apply_symm_apply _ _)
    (by unfold affineCoordinateTensorComparison; exact Equiv.apply_symm_apply _ _)
    (by unfold ModuleCat.extendScalarsComp; exact Equiv.apply_symm_apply _ _)
    (by unfold perfectHomTensorComp; exact Equiv.apply_symm_apply _ _)
    (affineCoordinateGammaComparison_comp a b c φ ψ p q hp hq hs)
  apply Iso.ext
  have hh := congrArg (fun e ↦ e.hom.app M) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id, Category.id_comp] using hh

/-- The chart model on the homotopy category. 
(blueprint: lem-pc-affine-coordinate-tensor-comparison)
-/
noncomputable abbrev affineCoordinateHomotopy (a : AffineComparisonCoordinate.{u, w}) :=
  affineCoordinateComplex a ⋙ HomotopyCategory.quotient _ (.up ℤ)

/-- The supplied model is localization of the concrete homotopy model. 
(blueprint: lem-pc-affine-coordinate-tensor-comparison)
-/
noncomputable def affineCoordinateHomotopyIso (a : AffineComparisonCoordinate.{u, w}) :
    a.H ≅ affineCoordinateHomotopy a ⋙ DerivedCategory.Qh :=
  affineCoordinateModelIso a ≪≫
    Functor.isoWhiskerLeft (affineCoordinateComplex a) (DerivedCategory.quotientCompQhIso _).symm

/-- The termwise comparison, factored through application of composite functors. 
(blueprint: lem-pc-affine-coordinate-tensor-comparison)
-/
noncomputable def affineCoordinateComplexComparison
    (a b : AffineComparisonCoordinate.{u, w}) (φ : a.A →+* b.A)
    (p : b.X ⟶ a.X)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom) :
    affineCoordinateComplex a ⋙ perfectHomTensorComplex p ≅
      (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙
        affineCoordinateComplex b := by
  let := perfectHomTensorAdditive p
  have : (ModuleCat.extendScalars φ).Additive :=
    ModuleCat.baseDerivedTensor_extendScalars_additive φ
  have : (tilde.functor a.A).Additive := ⟨by intros; exact tilde.map_add _ _⟩
  have : (tilde.functor b.A).Additive := ⟨by intros; exact tilde.map_add _ _⟩
  have : (Scheme.Modules.pushforward a.σ.hom).Additive := inferInstance
  have : (Scheme.Modules.pushforward b.σ.hom).Additive := inferInstance
  have : (affineCoordinateModules a).Additive := by
    change (tilde.functor a.A ⋙ Scheme.Modules.pushforward a.σ.hom).Additive
    infer_instance
  have : (affineCoordinateModules b).Additive := by
    change (tilde.functor b.A ⋙ Scheme.Modules.pushforward b.σ.hom).Additive
    infer_instance
  exact Functor.isoWhiskerRight (affineCoordinateComplexFactorIso a).symm
      (perfectHomTensorComplex p) ≪≫
    Functor.mapHomologicalComplexCompIso (affineCoordinateTensorComparison a b φ p hp)
      (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.extendScalars φ ⋙ affineCoordinateModules b)) (.up ℤ)).symm ≪≫
    Functor.isoWhiskerLeft ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ))
      (affineCoordinateComplexFactorIso b)

/-- Termwise comparison components are the underived module mate.
Source: the termwise construction; Stacks Project, Tag 01I9.
(blueprint: lem-pc-affine-coordinate-tensor-comparison). -/
theorem affineCoordinateComplexComparison_hom_f
    (a b : AffineComparisonCoordinate.{u, w}) (φ : a.A →+* b.A)
    (p : b.X ⟶ a.X)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
    (M : CochainComplex (ModuleCat.{u} a.A) ℤ) (n : ℤ) :
    ((affineCoordinateComplexComparison a b φ p hp).hom.app M).f n =
      (affineCoordinateTensorComparison a b φ p hp).hom.app (M.X n) := by
  change (Scheme.Modules.tensorPullback p).map (𝟙 _) ≫
    (affineCoordinateTensorComparison a b φ p hp).hom.app (M.X n) ≫ 𝟙 _ = _
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Category.comp_id]

/-- Mapping a complex in affine coordinates then passing to homotopy. 
(blueprint: lem-pc-affine-coordinate-tensor-comparison)
-/
theorem affineCoordinateHomotopy_map (a : AffineComparisonCoordinate.{u, w})
    {M N : CochainComplex (ModuleCat.{u} a.A) ℤ} (f : M ⟶ N) :
    (affineCoordinateHomotopy a).map f =
      (HomotopyCategory.quotient _ (.up ℤ)).map ((affineCoordinateComplex a).map f) := rfl

/-- The termwise mate, followed by the homotopy quotient. 
(blueprint: lem-pc-affine-coordinate-tensor-comparison)
-/
noncomputable def affineCoordinateHomotopyComparison
    (a b : AffineComparisonCoordinate.{u, w}) (φ : a.A →+* b.A)
    (p : b.X ⟶ a.X)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom) :
    affineCoordinateHomotopy a ⋙ perfectHomTensorHomotopy p ≅
      (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙
        affineCoordinateHomotopy b := by
  let := perfectHomTensorAdditive p
  exact Functor.associator (affineCoordinateComplex a)
      (HomotopyCategory.quotient _ (.up ℤ)) (perfectHomTensorHomotopy p) ≪≫
    Functor.isoWhiskerLeft (affineCoordinateComplex a)
      ((Scheme.Modules.tensorPullback p).mapHomotopyCategoryFactors (.up ℤ)) ≪≫
    (Functor.associator (affineCoordinateComplex a) (perfectHomTensorComplex p)
      (HomotopyCategory.quotient _ (.up ℤ))).symm ≪≫
    Functor.isoWhiskerRight (affineCoordinateComplexComparison a b φ p hp)
      (HomotopyCategory.quotient _ (.up ℤ))

/-- The homotopy comparison evaluates to the quotient of the complex comparison.
Source: the termwise construction and homotopy quotient; Stacks Project, Tag 01I9.
(blueprint: lem-pc-affine-coordinate-tensor-comparison). -/
theorem affineCoordinateHomotopyComparison_hom_app
    (a b : AffineComparisonCoordinate.{u, w}) (φ : a.A →+* b.A)
    (p : b.X ⟶ a.X)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
    (M : CochainComplex (ModuleCat.{u} a.A) ℤ) :
    (affineCoordinateHomotopyComparison a b φ p hp).hom.app M =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((affineCoordinateComplexComparison a b φ p hp).hom.app M) := by
  rfl

private theorem perfectHomTensorComplexComp_hom_app_f {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ) (n : ℤ) :
    ((perfectHomTensorComplexComp f g).hom.app K).f n =
      (perfectHomTensorComp f g).hom.app (K.X n) := by
  let := perfectHomTensorAdditive f
  let := perfectHomTensorAdditive g
  let := perfectHomTensorAdditive (f ≫ g)
  rw [perfectHomTensorComplexComp]
  exact Functor.mapHomologicalComplexCompIso_hom_app_f _ _ _ _

private theorem affineCoordinateComplex_map_f (a : AffineComparisonCoordinate.{u, w})
    {M N : CochainComplex (ModuleCat.{u} a.A) ℤ} (f : M ⟶ N) (n : ℤ) :
    ((affineCoordinateComplex a).map f).f n = (affineCoordinateModules a).map (f.f n) := rfl

private theorem affineCoordinateComplexComparison_comp_hom
    (a b c : AffineComparisonCoordinate.{u, w})
    (φ : a.A →+* b.A) (ψ : b.A →+* c.A) (p : b.X ⟶ a.X) (q : c.X ⟶ b.X)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
    (hq : c.σ.hom ≫ q = Spec.map (CommRingCat.ofHom ψ) ≫ b.σ.hom)
    (hs : c.σ.hom ≫ (q ≫ p) = Spec.map (CommRingCat.ofHom (ψ.comp φ)) ≫ a.σ.hom)
    (M : CochainComplex (ModuleCat.{u} a.A) ℤ) :
    (perfectHomTensorComplex q).map
        ((affineCoordinateComplexComparison a b φ p hp).hom.app M) ≫
        (affineCoordinateComplexComparison b c ψ q hq).hom.app
          (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M) =
      (perfectHomTensorComplexComp q p).hom.app ((affineCoordinateComplex a).obj M) ≫
        (affineCoordinateComplexComparison a c (ψ.comp φ) (q ≫ p) hs).hom.app M ≫
        (affineCoordinateComplex c).map
          ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp φ ψ) (.up ℤ)).hom.app M) := by
  let := perfectHomTensorAdditive q
  ext n : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    affineCoordinateComplexComparison_hom_f, perfectHomTensorComplexComp_hom_app_f,
    affineCoordinateComplex_map_f, NatIso.mapHomologicalComplex_hom_app_f]
  change (Scheme.Modules.tensorPullback q).map
      ((affineCoordinateTensorComparison a b φ p hp).hom.app (M.X n)) ≫
      (affineCoordinateTensorComparison b c ψ q hq).hom.app
        ((ModuleCat.extendScalars φ).obj (M.X n)) =
    (perfectHomTensorComp q p).hom.app ((affineCoordinateModules a).obj (M.X n)) ≫
      (affineCoordinateTensorComparison a c (ψ.comp φ) (q ≫ p) hs).hom.app (M.X n) ≫
      (affineCoordinateModules c).map ((ModuleCat.extendScalarsComp φ ψ).hom.app (M.X n))
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] using congrArg Iso.hom
    (affineCoordinateTensorComparison_comp a b c φ ψ p q hp hq hs (M.X n))

/-- The same composition equation on concrete homotopy models.
Source: Stacks Project, Tags 01I9, 08DW and 0D5S.
(blueprint: lem-pc-affine-coordinate-tensor-comparison).
Proof: map the underived equality termwise to complexes and apply the homotopy
quotient. The factor comparisons have identity components. At each degree the
remaining equality is exactly affineCoordinateTensorComparison_comp. -/
theorem affineCoordinateHomotopyComparison_comp
    (a b c : AffineComparisonCoordinate.{u, w})
    (φ : a.A →+* b.A) (ψ : b.A →+* c.A) (p : b.X ⟶ a.X) (q : c.X ⟶ b.X)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
    (hq : c.σ.hom ≫ q = Spec.map (CommRingCat.ofHom ψ) ≫ b.σ.hom)
    (hs : c.σ.hom ≫ (q ≫ p) = Spec.map (CommRingCat.ofHom (ψ.comp φ)) ≫ a.σ.hom)
    (M : CochainComplex (ModuleCat.{u} a.A) ℤ) :
    (perfectHomTensorHomotopy q).mapIso
        ((affineCoordinateHomotopyComparison a b φ p hp).app M) ≪≫
        (affineCoordinateHomotopyComparison b c ψ q hq).app
          (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M) =
      (perfectHomTensorHomotopyComp q p).app ((affineCoordinateHomotopy a).obj M) ≪≫
        (affineCoordinateHomotopyComparison a c (ψ.comp φ) (q ≫ p) hs).app M ≪≫
        (affineCoordinateHomotopy c).mapIso
          ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp φ ψ) (.up ℤ)).app M) := by
  let := perfectHomTensorAdditive p
  let := perfectHomTensorAdditive q
  let := perfectHomTensorAdditive (q ≫ p)
  apply Iso.ext
  let π := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings c.X.toRingedSpace)) (.up ℤ)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    affineCoordinateHomotopyComparison_hom_app,
    affineCoordinateHomotopy_map]
  erw [perfectHomTensorHomotopy_map,
    perfectHomTensorHomotopyComp_hom_app q p ((affineCoordinateComplex a).obj M)]
  rw [← π.map_comp, ← π.map_comp, ← π.map_comp]
  apply congrArg π.map
  exact affineCoordinateComplexComparison_comp_hom a b c φ ψ p q hp hq hs M

end AlgebraicGeometry
