/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # A direct-image test for tensor vanishing under an open immersion

Source: Stacks Project, Tags 08CG and 08DX.
(blueprint: lem-pc-open-immersion-tensor-vanishing-test).
-/

@[expose] public section

universe u w wY

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace AlgebraicGeometry

private noncomputable local instance (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- A single tensor-cohomology vanishing test descends along an open immersion.
Source: Stacks Project, Tags 08CG and 08DX, exact restriction and the open-immersion
counit. (blueprint: lem-pc-open-immersion-tensor-vanishing-test).

Proof: Choose the K-flat representative C and representing isomorphism in h.
The tensor pullback preserves K-flatness (Tag 06YC); the uniqueness of left
adjoints identifies that functor with open restriction R. Transport K-flatness
through the termwise complex isomorphism. The exact-functor localization
comparison identifies Q(R(C)) with R(E), with independent localization universes.
Transport the monoidal structure of module pullback to R. Its inverse tensorator,
followed by the open-immersion counit R(j_*G) ≅ G, gives a natural isomorphism
(tensorRight (j_*G)) followed by R ≅ R followed by (tensorRight G).
Tensor with a sheaf in degree zero is termwise tensor (the bifunctor-single
comparison), so mapping this natural isomorphism to complexes identifies the
restriction of C tensor j_*G[0] with R(C) tensor G[0]. Exact restriction commutes
with homology and preserves zero objects. Apply it to the vanishing in h and
transport along this complex comparison. These data witness the conclusion.
For empty schemes or zero sheaves the same comparisons exist and the homology
is zero; no boundedness or quasi-coherence is used. -/
theorem openImmersion_tensor_vanishing_test {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (G : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (i : ℤ)
    (h : schemeDerivedTensorCohomologyVanishes X E ((Scheme.Modules.pushforward j).obj G) i) :
    let R : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings Y.toRingedSpace) := Scheme.Modules.restrictFunctor j
    letI : R.Additive := ⟨by intros; rfl⟩
    letI : PreservesFiniteLimits R := by
      dsimp [R, Scheme.Modules.restrictFunctor]
      infer_instance
    letI : PreservesFiniteColimits R := by
      let H : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
          SheafOfModules.{u} (moduleRings X.toRingedSpace) := Scheme.Modules.pushforward j
      have adj : R ⊣ H := Scheme.Modules.restrictAdjunction j
      have : R.IsLeftAdjoint := adj.isLeftAdjoint
      infer_instance
    schemeDerivedTensorCohomologyVanishes Y (R.mapDerivedCategory.obj E) G i := by
  dsimp only
  let R : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y.toRingedSpace) := Scheme.Modules.restrictFunctor j
  have : R.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits R := by
    dsimp [R, Scheme.Modules.restrictFunctor]
    infer_instance
  let H : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := Scheme.Modules.pushforward j
  have adj : R ⊣ H := Scheme.Modules.restrictAdjunction j
  have : R.IsLeftAdjoint := adj.isLeftAdjoint
  have : (Scheme.Modules.pullback j).Monoidal := Scheme.Modules.pullbackMonoidal j
  have : R.Monoidal :=
    Functor.Monoidal.transport (Scheme.Modules.restrictFunctorIsoPullback j).symm
  obtain ⟨C, hC, ⟨eC⟩, hz⟩ := h
  let T := Scheme.Modules.tensorPullback j
  have : T.IsLeftAdjoint := ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction j⟩
  have : T.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
    (by rw [CategoryTheory.rightExactFunctor_iff]; infer_instance)
  let t : T ≅ R := (Scheme.Modules.nonempty_tensorPullbackAdjunction j).some.leftAdjointUniq
    (Scheme.Modules.restrictAdjunction j)
  have hTC : CochainComplex.IsKFlatTensor (R := Y.sheaf)
      ((T.mapHomologicalComplex (.up ℤ)).obj C) := by
    have h' := CochainComplex.isKFlat_pullback j.base Y.sheaf X.sheaf ⟨j.c⟩ C hC
    convert h' using 1
    rfl
  have hRC : CochainComplex.IsKFlatTensor (R := Y.sheaf)
      ((R.mapHomologicalComplex (.up ℤ)).obj C) := by
    intro F hF n
    exact (hTC F hF n).of_iso
      (((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj F).mapIso
        ((NatIso.mapHomologicalComplex t (.up ℤ)).app C))
  refine ⟨(R.mapHomologicalComplex (.up ℤ)).obj C, hRC,
    ⟨(R.mapDerivedCategoryFactors.app C).symm ≪≫ R.mapDerivedCategory.mapIso eC⟩, ?_⟩
  let counit : R.obj (H.obj G) ≅ G := (Scheme.Modules.restrictFunctorAdjCounitIso j).app G
  let e : MonoidalCategory.tensorRight (H.obj G) ⋙ R ≅
      R ⋙ MonoidalCategory.tensorRight G :=
    NatIso.ofComponents
      (fun F ↦ (Functor.Monoidal.μIso R F (H.obj G)).symm ≪≫
        MonoidalCategory.whiskerLeftIso (R.obj F) counit)
      (by
        intro F F' f
        change R.map (f ▷ H.obj G) ≫ Functor.OplaxMonoidal.δ R F' (H.obj G) ≫
          R.obj F' ◁ counit.hom =
            Functor.OplaxMonoidal.δ R F (H.obj G) ≫ R.obj F ◁ counit.hom ≫ R.map f ▷ G
        rw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
        simp only [whisker_exchange])
  let N := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (H.obj G)
  let K := CochainComplex.mapBifunctor C N (MonoidalCategory.curriedTensor _)
  let src := CochainComplex.mapBifunctorSingle₂Iso (MonoidalCategory.curriedTensor _)
    (H.obj G) C
  let dst := CochainComplex.mapBifunctorSingle₂Iso (MonoidalCategory.curriedTensor _)
    G ((R.mapHomologicalComplex (.up ℤ)).obj C)
  let cmp : (R.mapHomologicalComplex (.up ℤ)).obj K ≅
      CochainComplex.mapBifunctor ((R.mapHomologicalComplex (.up ℤ)).obj C)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)
        (MonoidalCategory.curriedTensor _) :=
    (R.mapHomologicalComplex (.up ℤ)).mapIso src ≪≫
      (NatIso.mapHomologicalComplex e (.up ℤ)).app C ≪≫ dst.symm
  have hzR := R.map_isZero hz
  have hzero : IsZero (((R.mapHomologicalComplex (.up ℤ)).obj K).homology i) := by
    exact hzR.of_iso ((R.mapHomologicalComplexHomologyIso (.up ℤ) i).app K)
  exact hzero.of_iso ((HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso cmp).symm

end AlgebraicGeometry
