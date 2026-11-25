/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.EtaleCohomology.TateTwist.Normalized
import WeilConjectures.EtaleCohomology.TateTwist.KummerLevelIndependence
import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine
import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection

/-! # The normalized Tate coefficient over a field
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private noncomputable def zmodScalarExtensionIso
    (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar N A hA) ≅
      forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
        ModuleCat.extendScalarsAddCommGrp A := by
  let f := Scheme.finiteEtaleTwistScalar N A hA
  let adj := ModuleCat.extendScalarsAddCommGrpAdj A
  let e (M : ModuleCat.{u + 1} (ZMod N)) (P : ModuleCat.{u + 1} A) :
      ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).obj M ⟶
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat).obj P) ≃
        (M ⟶ (ModuleCat.restrictScalars f).obj P) :=
    { toFun := fun g ↦ ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars f).obj P)
        (AddMonoidHom.toZModLinearMap N (M := M)
          (M₁ := (ModuleCat.restrictScalars f).obj P) g.hom)
      invFun := fun g ↦ AddCommGrpCat.ofHom g.hom.toAddMonoidHom
      left_inv := fun g ↦ rfl
      right_inv := fun g ↦ by ext; rfl }
  let adj' : (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
      ModuleCat.extendScalarsAddCommGrp A) ⊣ ModuleCat.restrictScalars f :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun M P ↦ (adj.homEquiv _ _).trans (e M P)
        homEquiv_naturality_left_symm := by
          intro M' M P g k
          change (adj.homEquiv _ _).symm
            ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).map g ≫
              (e M P).symm k) = _
          exact adj.homEquiv_naturality_left_symm _ _
        homEquiv_naturality_right := by
          intro M P P' g k
          change e M P' (adj.homEquiv _ _ (g ≫ k)) = _
          rw [adj.homEquiv_naturality_right]
          rfl }
  exact (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} f).leftAdjointUniq adj'

/-- The finite twist line is the existing abelian-sheaf scalar extension. -/
private noncomputable def finiteEtaleLineAbIso
    (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    Scheme.finiteEtaleTateLine T N A hA ≅
      (AlgebraicGeometry.Etale.extendScalars A T).obj (T.rootsOfUnitySheaf N) :=
  (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso
    (Functor.isoWhiskerLeft (Scheme.finiteEtaleMuModulePresheaf T N)
      (zmodScalarExtensionIso N A hA))

private theorem normalized_zero_tensor_unit
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ] (k : Type u) [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] :
    Nonempty
      (((derivedTensor (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
        ((R(AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k)))^![Λ]).obj
            (constantComplex Λ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k)))))).obj
        ((tateObject Λ (Spec (.of k)) 1)⟦(2 : ℤ)⟧) ≅ constantComplex Λ (Spec (.of k))) := by
  let Y := Spec (.of k)
  let A := AffineSpace (ULift.{u} (Fin 1)) Y
  let s := AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y
  let H := R(s)^![Λ]
  let P := L((s)^*[ModuleCat.{u + 1} Λ])
  let L := (tateObject Λ A 1)⟦(2 : ℤ)⟧
  obtain ⟨LI, ⟨e⟩, ⟨e'⟩⟩ := (isInvertible_tateObject Λ A 1).shift (2 : ℤ)
  let cop := (derivedTensorRightCompRightDerivedUpperShriekIso Λ s L LI e' e).app
    (constantComplex Λ A)
  obtain ⟨n⟩ := nonempty_iso_rightDerivedUpperShriek_affineLineZero Λ (𝟙 Y)
  let q : H.obj L ≅ constantComplex Λ Y :=
    H.mapIso ((shiftFunctor _ (2 : ℤ)).mapIso
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) A _)).symm ≪≫ n
  let r : P.obj L ≅ (tateObject Λ Y 1)⟦(2 : ℤ)⟧ :=
    (P.commShiftIso (2 : ℤ)).app _ ≪≫
      (shiftFunctor _ (2 : ℤ)).mapIso (leftDerivedUpperStarTateObjectIso s 1)
  exact ⟨((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj _).mapIso r.symm ≪≫
    cop.symm ≪≫ H.mapIso (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) A L) ≪≫ q⟩

/-- Over a field the zero-section normalization determines the degree-one coefficient. -/
theorem nonempty_normalizedTateLineOverField
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ] (N : ℕ) (_hN : 0 < N) (hΛ : (N : Λ) = 0)
    (k : Type u) [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
    (hk : IsUnit (N : Γ(Spec (.of k), ⊤))) :
    Nonempty (tateObject Λ (Spec (.of k)) 1 ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateLine (Spec (.of k)) N Λ hΛ))  := by
  have : NeZero (ringChar Λ) := ⟨CharP.ringChar_ne_zero_of_finite Λ⟩
  let Y := Spec (.of k)
  let W := (R(AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)^![Λ]).obj
      (constantComplex Λ (AffineSpace (ULift.{u} (Fin 1)) Y))
  let T := (tateObject Λ Y 1)⟦(2 : ℤ)⟧
  let C := (tateTwistObject Λ Y 1)⟦(2 : ℤ)⟧
  obtain ⟨eT⟩ := normalized_zero_tensor_unit Λ k
  have eC : Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj W).obj C ≅
      constantComplex Λ Y) := by
    let := hasTateTwist Λ
    exact normalized_zero_tensor_unit Λ k
  obtain ⟨eC⟩ := eC
  obtain ⟨b⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) Y
  let e : T ≅ C :=
    (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) Y T).symm ≪≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) Y).mapIso
        (((b.app C).app W ≪≫ eC).symm)).app T ≪≫
      derivedTensorAssociator (ModuleCat.{u + 1} Λ) Y C W T ≪≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj C).mapIso eT ≪≫
      derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) Y C
  let e0 : tateObject Λ Y 1 ≅ tateTwistObject Λ Y 1 :=
    (shiftFunctor _ (2 : ℤ)).preimageIso e
  let ef := (finiteEtaleLineAbIso Y N Λ hΛ) ≪≫
    extendScalarsRootsOfUnityIsoTateTwistSheaf Λ N hΛ hk
  exact ⟨e0 ≪≫ tateTwistObjectIsoSingleFunctor Λ Y 1 ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso ef.symm⟩

end AlgebraicGeometry.Etale
