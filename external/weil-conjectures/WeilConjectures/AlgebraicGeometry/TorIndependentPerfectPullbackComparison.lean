/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PullbackStalkTensorComparison
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Algebra.Homology.TorIndependentKFlatTensorComparison
import WeilConjectures.AlgebraicGeometry.PullbackStalkTensorFlat
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk

/-! # Tor-independent perfect pullback comparison at a stalk

Source: Stacks Project, Tag 08IB, local affine Tor-independent tensor comparison
(blueprint: lem-pc-tor-independent-perfect-pullback-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u₁ w₁
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry


private theorem stalk_additive (Y : RingedSpace.{u₁}) (y : Y) :
    (RingedSpace.moduleStalkFunctor Y y).Additive := by
  constructor
  intro M N a b
  ext m
  change (TopCat.Presheaf.stalkFunctor Ab y).map
    ((PresheafOfModules.toPresheaf _).map (a + b).val) m = _
  change (TopCat.Presheaf.stalkFunctor Ab y).map
    ((PresheafOfModules.toPresheaf _).map (a.val + b.val)) m = _
  rw [Functor.map_add, Functor.map_add]
  rfl

private theorem kFlat_pullback_stalk_cohomology
    {X S T : Scheme.{u₁}} (f : X ⟶ S) (g : T ⟶ S)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₁}
      (SheafOfModules.{u₁} (moduleRings (Limits.pullback f g).toRingedSpace))]
    (P : schemeDerivedCategory X) (z : ↥(Limits.pullback f g))
    (K : CochainComplex (SheafOfModules.{u₁} (moduleRings X.toRingedSpace)) ℤ)
    (hK : K.IsKFlatTensor) (eK : DerivedCategory.Q.obj K ≅ P) (i : ℤ) :
    Nonempty
      ((PullbackStalkTensor.stalkTensorComplex f g z K).homology i ≅
        (RingedSpace.moduleStalkFunctor (Limits.pullback f g).toRingedSpace z).obj
          ((DerivedCategory.homologyFunctor _ i).obj
            ((derivedPullback (pullback.fst f g)).obj P))) := by
  classical
  let Y := Limits.pullback f g
  let k := pullback.fst f g
  let A := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)
  let B := SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)
  obtain ⟨_, _, _, _, _, _, _, F, hF, hmap, hAdd, ε, _, _, hcompute⟩ :=
    derivedPullback_spec k
  have hF' : F = Scheme.Modules.tensorPullback k :=
    CategoryTheory.Functor.ext hF (fun _ _ a ↦ hmap a)
  subst F
  let F := Scheme.Modules.tensorPullback k
  have : F.Additive := hAdd
  let Fc := F.mapHomologicalComplex (.up ℤ)
  have : IsIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj K)) := hcompute K hK
  let c : (derivedPullback k).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (Fc.obj K) :=
    (derivedPullback k).mapIso ((DerivedCategory.quotientCompQhIso A).symm.app K) ≪≫
      asIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj K)) ≪≫
      DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app K) ≪≫
      (DerivedCategory.quotientCompQhIso B).app (Fc.obj K)
  let St := RingedSpace.moduleStalkFunctor Y.toRingedSpace z
  have : St.PreservesZeroMorphisms :=
    RingedSpace.moduleStalkFunctor_preservesZeroMorphisms Y.toRingedSpace z
  have : St.PreservesHomology := Functor.preservesHomology_of_map_exact St (by
    intro V hV
    exact ((RingedSpace.module_stalk_exact Y.toRingedSpace V.f).2.2.2.2
      V.X₃ V.f V.g V.zero).mp hV z)
  let h : St.obj ((Fc.obj K).homology i) ≅
      St.obj ((DerivedCategory.homologyFunctor B i).obj ((derivedPullback k).obj P)) :=
    St.mapIso ((DerivedCategory.homologyFunctorFactors B i).symm.app (Fc.obj K) ≪≫
      (DerivedCategory.homologyFunctor B i).mapIso c.symm ≪≫
      (DerivedCategory.homologyFunctor B i).mapIso ((derivedPullback k).mapIso eK))
  let hSt : ((St.mapHomologicalComplex (.up ℤ)).obj (Fc.obj K)).homology i ≅
      St.obj ((Fc.obj K).homology i) := ((Fc.obj K).sc i).mapHomologyIso St
  obtain ⟨d, _⟩ := Scheme.Modules.exists_tensorPullback_stalk_iso k z
  have : (ModuleCat.extendScalars.{u₁, u₁, u₁} (k.stalkMap z).hom).Additive :=
    ModuleCat.baseDerivedTensor_extendScalars_additive _
  have : (RingedSpace.moduleStalkFunctor X.toRingedSpace (k z)).PreservesZeroMorphisms :=
    RingedSpace.moduleStalkFunctor_preservesZeroMorphisms X.toRingedSpace (k z)
  have : St.Additive := stalk_additive Y.toRingedSpace z
  have : (RingedSpace.moduleStalkFunctor X.toRingedSpace (k z)).Additive :=
    stalk_additive X.toRingedSpace (k z)
  let t := ((Functor.mapHomologicalComplexCompIso
    (Iso.refl (RingedSpace.moduleStalkFunctor X.toRingedSpace (k z) ⋙
      ModuleCat.extendScalars.{u₁, u₁, u₁} (k.stalkMap z).hom)) (.up ℤ)).app K) ≪≫
    (NatIso.mapHomologicalComplex d.symm (.up ℤ)).app K ≪≫
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ St)) (.up ℤ)).app K).symm
  have ht : PullbackStalkTensor.stalkTensorComplex f g z K ≅
      ((St.mapHomologicalComplex (.up ℤ)).obj (Fc.obj K)) := by
    let e := eqToIso (congrArg
      (fun a : PullbackStalkTensor.A f g z →+* PullbackStalkTensor.C f g z ↦
        ((ModuleCat.extendScalars.{u₁, u₁, u₁} a).mapHomologicalComplex (.up ℤ)).obj
          (PullbackStalkTensor.stalkComplex f g z K))
      (PullbackStalkTensor.tensorToStalk_spec f g z).1)
    exact e ≪≫ t
  exact ⟨(HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso ht ≪≫ hSt ≪≫ h⟩

/-- For a Tor-independent square, the canonical base-derived tensor comparison
for a perfect object is an isomorphism at every pullback stalk in every degree.
The comparison is expressed in K-flat coordinates by `IsComparisonIso`, using
exactly the canonical map of `BaseDerivedTensorCohomologyModel`; invertibility
is invariant under the identification with the actual derived pullback stalk.

Source: Stacks Project, perfect.tex, Tag 08IB, local affine reduction
(blueprint: lem-pc-tor-independent-perfect-pullback-comparison).

Proof (the node's three steps):
1. Fix z and put R = O_{S,s}, A = O_{X,x}, B = O_{T,t}, C = O_{X',z}.
   On an affine neighbourhood of x, perfectness gives a bounded finite-projective
   model Q, by lem-pc-perfect-affine-bounded-projective.
2. The hypothesis gives Tor_i^R(A,B) = 0 for i > 0. Apply
   lem-pc-tor-independent-projective-complex-tensor to Q and the localization
   A tensor-over-R B -> C. Its map is the model's localizedComparison.
3. Restrict derived pullback to this neighbourhood by
   lem-pc-affine-derived-pullback-tensor-tilde. Its strictly perfect model is
   termwise flat, so lemma-coherent-base-change-invertible-sheaves--2 computes its derived
   pullback termwise. Apply lem-weil-pbc-module-stalk-pullback degreewise to
   identify the target with Q tensor-over-A C. The ring map to C is a
   localization by the affine description of the fibre product; exactness of
   localization (lem-weil-pbc-localization-module-exact) commutes it with
   cohomology. These natural identifications identify the canonical map with
   Step 2. For any other K-flat representative, a common resolution and
   functoriality of derived tensor and pullback transport the same comparison.
   Postcomposition with any isomorphism of target coordinates preserves IsIso. -/
theorem torIndependent_perfect_pullback_comparison
    {X S T : Scheme.{u₁}} (f : X ⟶ S) (g : T ⟶ S)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w₁} (SheafOfModules.{u₁} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{w₁}
      (SheafOfModules.{u₁} (moduleRings (Limits.pullback f g).toRingedSpace))]
    (hTor : PullbackStalkTensor.IsTorIndependent f g)
    (P : schemeDerivedCategory X) (hP : Scheme.IsPerfect X P) :
    ∀ z : ↥(Limits.pullback f g), PullbackStalkTensor.IsComparisonIso f g P z := by
  -- The algebraic argument applies to all K-flat stalks; perfection is unnecessary here.
  have _perfect := hP
  intro z
  change ∀ K, K.IsKFlatTensor → Nonempty (DerivedCategory.Q.obj K ≅ P) → ∀ i, _
  intro K hK ⟨eK⟩ i
  refine ⟨kFlat_pullback_stalk_cohomology f g P z K hK eK i, ?_⟩
  intro e
  let := PullbackStalkTensor.leftAlgebra f g z
  let := PullbackStalkTensor.rightAlgebra f g z
  let := PullbackStalkTensor.tensorAlgebra f g z
  let := HasDerivedCategory.standard (ModuleCat.{u₁} (PullbackStalkTensor.R f g z))
  let := HasDerivedCategory.standard (ModuleCat.{u₁} (PullbackStalkTensor.B f g z))
  have hstalk := (RingedSpace.isKFlat_iff_stalk_isKFlat X.toRingedSpace K).mp hK
    ((pullback.fst f g) z)
  have hTor' := hTor ((pullback.fst f g) z) ((pullback.snd f g) z)
    (PullbackStalkTensor.point_eq f g z)
  have hflat := pullback_stalk_tensor_flat g f z rfl rfl
    (PullbackStalkTensor.tensorToStalk_spec f g z).1
    (PullbackStalkTensor.tensorToStalk_spec f g z).2
  have : IsIso ((PullbackStalkTensor.cohomologyModel f g z K).localizedComparison i) :=
    ModuleCat.localizedComparison_isIso_of_torIndependent_kFlat hTor'
      (PullbackStalkTensor.stalkComplex f g z K) hstalk hflat
      (PullbackStalkTensor.cohomologyModel f g z K) i
  infer_instance

end AlgebraicGeometry
