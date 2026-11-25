/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import WeilConjectures.AlgebraicGeometry.FiniteTorDimension
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.AlgebraicGeometry.AffineTorAmplitudeCriterion
import WeilConjectures.AlgebraicGeometry.OpenImmersionTensorVanishingTest
import all WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Tor bounds for an affine module model

Source: Stacks Project, Tags 08CG, 08E9 and 08DX.
(blueprint: lem-pc-affine-local-sheafification-tor-amplitude).
-/

@[expose] public section

universe u w wR

open CategoryTheory CategoryTheory.Limits

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace AlgebraicGeometry.Scheme

noncomputable def affine_cancel (S : Scheme.{u}) (U : S.Opens) (hU : IsAffineOpen U) :
    affinePerfectSheafification S U hU ⋙ (Modules.overEquiv U).functor ⋙
      Modules.restrictFunctor hU.isoSpec.inv ≅ tilde.functor (S.presheaf.obj (.op U)) := by
  let T := tilde.functor (S.presheaf.obj (.op U))
  let H := Modules.restrictFunctor hU.isoSpec.hom
  let B := Modules.restrictFunctor hU.isoSpec.inv
  let E := Modules.overEquiv U
  change ((T ⋙ H) ⋙ E.inverse) ⋙ E.functor ⋙ B ≅ T
  exact Functor.isoWhiskerLeft (T ⋙ H) (Functor.isoWhiskerRight E.counitIso B) ≪≫
    Functor.isoWhiskerLeft T
      ((Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom).symm ≪≫
        Modules.restrictFunctorCongr hU.isoSpec.inv_hom_id ≪≫ Modules.restrictFunctorId) ≪≫
    Functor.rightUnitor T

/-- Tor bounds on an open W pass to a module model on an affine subopen U.
Source: Stacks Project, Tags 08CG, 08E9(1), 08DX(2), and 09U8.
(blueprint: lem-pc-affine-local-sheafification-tor-amplitude).

Proof: Write the interval [a,b] supplied by the finite Tor hypothesis on W.
For each module sheaf G on U, regard G as a sheaf on W by direct image under
U.toScheme -> W.toScheme. Test the Tor bound on that direct image, and restrict
back to U. Exact restriction preserves derived tensor and homology; the
restriction of the direct image is G. Composition of derived open pullbacks
identifies the restricted object with the pullback of K from S to U. Thus the
same interval bounds all its tensors with G. Transport along U.isoSpec and
Modules.overEquiv U: these exact equivalences identify the structure sheaves,
tensor products and cohomology. The representing isomorphism hP identifies the
object with the associated complex of P. Test on associated sheaves of ring
modules and use the affine Tor-amplitude criterion (08E9(1)). Exact faithful
associated sheafification detects zero homology modules, proving Tor amplitude
[a,b] for Q(P). Empty opens and zero rings give zero modules, and no boundedness
or pseudo-coherence of P is used. -/
theorem finiteTorAmplitude_of_affine_sheafification_of_open_tor (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ V : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over V))]
    (U : S.Opens) (hU : IsAffineOpen U)
    [HasDerivedCategory.{wR} (ModuleCat.{u} (S.presheaf.obj (.op U)))]
    (K : schemeDerivedCategory S)
    (P : CochainComplex (ModuleCat.{u} (S.presheaf.obj (.op U))) ℤ)
    (hP : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification S U hU).mapHomologicalComplex (.up ℤ)).obj P)))
    (W : S.Opens) (hUW : U ≤ W)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (hTor : HasFiniteTorDimension W.toScheme ((derivedPullback W.ι).obj K)) :
    ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn
      (ModuleCat.{u} (S.presheaf.obj (.op U))) a b (DerivedCategory.Q.obj P) := by
  let : HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (moduleRings (Spec (S.presheaf.obj (.op U))).toRingedSpace)) :=
    HasDerivedCategory.standard _
  let Z := Spec (S.presheaf.obj (.op U))
  let j : Z ⟶ W.toScheme := hU.isoSpec.inv ≫ S.homOfLE hUW
  let RW : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
    Modules.restrictFunctor W.ι
  have : RW.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits RW := by
    dsimp [RW, Modules.restrictFunctor]
    infer_instance
  have : RW.IsLeftAdjoint := by
    let H : SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings S.toRingedSpace) := Modules.pushforward W.ι
    exact (show RW ⊣ H from Modules.restrictAdjunction W.ι).isLeftAdjoint
  let RJ : SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Z.toRingedSpace) := Modules.restrictFunctor j
  have : RJ.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits RJ := by
    dsimp [RJ, Modules.restrictFunctor]
    infer_instance
  have : RJ.IsLeftAdjoint := by
    let H : SheafOfModules.{u} (moduleRings Z.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) := Modules.pushforward j
    exact (show RJ ⊣ H from Modules.restrictAdjunction j).isLeftAdjoint
  let A := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U
  let E : SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Modules.overEquiv U
  have : E.functor.Additive := ⟨by intros; rfl⟩
  let T : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Z.toRingedSpace) :=
    Modules.restrictFunctor hU.isoSpec.inv
  have : T.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits T := by
    dsimp [T, Modules.restrictFunctor]
    infer_instance
  let H : SheafOfModules.{u} (moduleRings Z.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Modules.pushforward hU.isoSpec.inv
  have adjT : T ⊣ H := Modules.restrictAdjunction hU.isoSpec.inv
  have : T.IsLeftAdjoint := adjT.isLeftAdjoint
  let B := E.functor ⋙ T
  have : B.Additive := inferInstance
  have : PreservesFiniteLimits B := comp_preservesFiniteLimits _ _
  have : B.IsLeftAdjoint := (E.toAdjunction.comp adjT).isLeftAdjoint
  let T' : SheafOfModules.{u} (moduleRings Z.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Modules.restrictFunctor hU.isoSpec.hom
  have : T'.Additive := ⟨by intros; rfl⟩
  have : HasBinaryBiproducts
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : PreservesBinaryBiproducts E.inverse :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : E.inverse.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let L : ModuleCat.{u} (S.presheaf.obj (.op U)) ⥤
      SheafOfModules.{u} (moduleRings Z.toRingedSpace) :=
    tilde.functor (S.presheaf.obj (.op U))
  have : L.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  have : (affinePerfectSheafification S U hU).Additive := by
    change (L ⋙ T' ⋙ E.inverse).Additive
    infer_instance
  obtain ⟨C, hC, ⟨eC⟩⟩ := AlgebraicGeometry.exists_kFlat_model S K
  obtain ⟨eCW⟩ := AlgebraicGeometry.open_pullback_model_iso W.ι C hC
  let eW : (derivedPullback W.ι).obj K ≅ RW.mapDerivedCategory.obj K :=
    (derivedPullback W.ι).mapIso eC.symm ≪≫ eCW ≪≫
      (RW.mapDerivedCategoryFactors.app C).symm ≪≫ RW.mapDerivedCategory.mapIso eC
  let θ : RW ⋙ RJ ≅ A ⋙ B := by
    exact (Modules.restrictFunctorComp j W.ι).symm ≪≫
      Modules.restrictFunctorCongr (by simp [j, Category.assoc]) ≪≫
      Modules.restrictFunctorComp hU.isoSpec.inv U.ι ≪≫
      Functor.isoWhiskerRight (Modules.overFunctorEquiv U).symm
        (Modules.restrictFunctor hU.isoSpec.inv)
  obtain ⟨eP⟩ := hP
  let e : RJ.mapDerivedCategory.obj ((derivedPullback W.ι).obj K) ≅
      DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (S.presheaf.obj (.op U)))
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) _ _ _ _
          (tilde.functor (S.presheaf.obj (.op U))) ⟨fun _ _ ↦ tilde.map_zero⟩
          (ComplexShape.up ℤ)).obj P) := by
    exact RJ.mapDerivedCategory.mapIso eW ≪≫
      (Functor.mapDerivedCategoryCompIso RW RJ).app K ≪≫
      (Functor.mapDerivedCategoryNatIso θ).app K ≪≫
      (Functor.mapDerivedCategoryCompIso A B).symm.app K ≪≫
      B.mapDerivedCategory.mapIso eP ≪≫ B.mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso
          (F := affinePerfectSheafification S U hU) (G := B) (H := L)
          (affine_cancel S U hU) (.up ℤ)).app P)
  obtain ⟨a, b, hab, hvan⟩ := hTor
  refine ⟨a, b, hab, (affine_torAmplitude_iff (S.presheaf.obj (.op U)) P a b hab).mp ?_⟩
  intro G i hi
  have hv := openImmersion_tensor_vanishing_test j
    ((derivedPullback W.ι).obj K) G i (hvan ((Modules.pushforward j).obj G) i hi)
  obtain ⟨D, hD, ⟨eD⟩, hz⟩ := hv
  exact ⟨D, hD, ⟨eD ≪≫ e⟩, hz⟩

end AlgebraicGeometry.Scheme
