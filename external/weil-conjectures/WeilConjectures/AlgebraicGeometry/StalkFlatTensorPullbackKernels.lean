/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlatPullback
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkChangeOfRings
import WeilConjectures.Algebra.Homology.InverseImageStalkScalarTransport
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits

/-! # Kernels of tensor pullback along stalkwise flat morphisms
Source: Stacks Project, Modules, Tag 02N4.
(blueprint: lem-sc-stalk-flat-tensor-pullback-kernels)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RingedSpace

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stalk_preservesFiniteLimits (X : RingedSpace.{u}) (x : X) :
    PreservesFiniteLimits (moduleStalkFunctor X x) := by
  let A := forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  have : PreservesFiniteLimits (moduleStalkFunctor X x ⋙ A) := by
    change PreservesFiniteLimits (SheafOfModules.toSheaf (moduleRings X) ⋙
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x))
    have hb : PreservesFiniteLimits
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := inferInstance
    exact comp_preservesFiniteLimits (SheafOfModules.toSheaf (moduleRings X)) _
  exact preservesFiniteLimits_of_reflects_of_preserves _ A

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stalk_jointlyReflectIsomorphisms (X : RingedSpace.{u}) :
    JointlyReflectIsomorphisms (moduleStalkFunctor X) := by
  constructor
  intro M N a ha
  let T := SheafOfModules.toSheaf (moduleRings X)
  have hs (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map (T.map a).hom) := by
    let A := forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) Ab.{u}
    exact A.map_isIso ((moduleStalkFunctor X x).map a)
  have : IsIso (T.map a) := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso (T.map a)
  exact isIso_of_reflects_iso a T

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensor pullback along a stalkwise flat morphism preserves kernels.
Source: Stacks Project, Modules, Tag 02N4, proof by stalks.
(blueprint: lem-sc-stalk-flat-tensor-pullback-kernels)

Proof: stalks preserve kernels. At x the inverse-image stalk comparison and the
change-of-rings tensor stalk comparison identify P(M)_x with extension of scalars
of M_(g(x)) along g's stalk map. The adjoint ring-map formula identifies that scalar
map with g.hom.stalkMap x. The prescribed map formula makes these comparisons
natural in M. Flat extension of scalars preserves kernels, so P(kernel a)_x,
with the stalk of P(kernel.ι a), is the kernel of (P.map a)_x. Thus the canonical
comparison P(kernel a) → kernel(P.map a) is an isomorphism on every stalk.
Stalks detect isomorphisms of module sheaves, so the comparison is an isomorphism
of sheaves. This is precisely preservation of the limit of parallelPair a 0;
additivity ensures P.map 0 = 0. No quasi-coherence assumption is used. -/
theorem stalkFlat_tensorModulePullback_preservesKernels
    {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (hg : ∀ x : X, (g.hom.stalkMap x).hom.Flat)
    (P : SheafOfModules.{u} (moduleRings Y) ⥤
      SheafOfModules.{u} (moduleRings X))
    (h : ∀ M, P.obj M = SheafOfModules.changeOfRings.{u, u, u}
      (CochainComplex.tensorPullbackRingMap
        g.hom.base X.sheaf
        Y.sheaf ⟨g.hom.c⟩)
      (TopCat.Sheaf.inverseImageModule g.hom.base
        Y.sheaf M))
    (hm : ∀ {M N} (a : M ⟶ N),
      P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap
          g.hom.base X.sheaf
          Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base
          Y.sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap g.hom.base
          Y.sheaf M a) ≫ eqToHom (h N).symm)
    [P.Additive] :
    ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
      PreservesLimit (parallelPair a 0) P := by
  classical
  let (x : X) := stalk_preservesFiniteLimits X x
  let (y : Y) := stalk_preservesFiniteLimits Y y
  let α := CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩
  have stalkPreserves (x : X) : PreservesFiniteLimits (P ⋙ moduleStalkFunctor X x) := by
    let f := g.hom.base
    let k := TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} f Y.presheaf x ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback CommRingCat.{u} f).obj Y.presheaf))
    let ψ := ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map α.hom).hom
    let ρ := ψ.comp k.hom
    have hρ : ρ = (g.hom.stalkMap x).hom := by
      have he : k ≫ (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map α.hom =
          g.hom.stalkMap x := by
        apply TopCat.Presheaf.stalk_hom_ext
        intro V hV
        dsimp only [k]
        simp only [Category.assoc]
        erw [TopCat.Presheaf.germ_stalkPullbackHom_assoc,
          TopCat.Presheaf.stalkFunctor_map_germ_assoc,
          TopCat.Presheaf.stalkFunctor_map_germ,
          AlgebraicGeometry.PresheafedSpace.stalkMap_germ]
        let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (TopologicalSpace.Opens.map f) CommRingCat.{u}
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
        have hu : adj.unit.app Y.sheaf ≫
            ((TopologicalSpace.Opens.map f).sheafPushforwardContinuous CommRingCat.{u}
              (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).map α =
            ⟨g.hom.c⟩ := by
          erw [← adj.homEquiv_unit]
          exact (adj.homEquiv Y.sheaf X.sheaf).apply_symm_apply ⟨g.hom.c⟩
        have huV := congrArg (fun t ↦ t.hom.app (Opposite.op V)) hu
        change (adj.unit.app Y.sheaf).hom.app (Opposite.op V) ≫
          α.hom.app (Opposite.op ((TopologicalSpace.Opens.map f).obj V)) =
            g.hom.c.app (Opposite.op V) at huV
        have hu0 : (adj.unit.app Y.sheaf).hom.app (Opposite.op V) =
            ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app
              Y.presheaf).app (Opposite.op V) ≫
              (toSheafify (Opens.grothendieckTopology X)
                ((TopCat.Presheaf.pullback CommRingCat.{u} f).obj Y.presheaf)).app
                  (Opposite.op ((TopologicalSpace.Opens.map f).obj V)) := by
          change ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map
            (adj.unit.app Y.sheaf)).app (Opposite.op V) = _
          dsimp only [adj, Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
          rw [Adjunction.map_restrictFullyFaithful_unit_app]
          simp [Adjunction.comp_unit_app, TopCat.Presheaf.pullbackPushforwardAdjunction,
            TopCat.Presheaf.pullback]
          rfl
        rw [hu0] at huV
        have hv := congrArg
          (fun t ↦ t ≫ X.presheaf.germ ((TopologicalSpace.Opens.map f).obj V) x hV) huV
        simp only [Category.assoc] at hv
        exact hv
      exact congrArg (fun t ↦ t.hom) he
    let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (show ρ.Flat from hρ ▸ hg x)
    obtain ⟨c, β, hβ, hc⟩ :=
      exists_ringed_inverseImage_stalk_scalar_transport X Y f α x
    obtain ⟨τ, _, hτ⟩ := SheafOfModules.stalkChangeOfRingsIso X.carrier
      (TopCat.Sheaf.inverseImageRing f Y.sheaf) X.sheaf α x
    let δ (M : Modules Y) :
        (ModuleCat.extendScalars ρ).obj ((moduleStalkFunctor Y (f x)).obj M) ≅
          (moduleStalkFunctor X x).obj (SheafOfModules.changeOfRings.{u, u, u} α
            (TopCat.Sheaf.inverseImageModule f Y.sheaf M)) :=
      β M ≪≫ τ (TopCat.Sheaf.inverseImageModule f Y.sheaf M)
    have hδ (M N : Modules Y) (a : M ⟶ N) :
        (ModuleCat.extendScalars ρ).map ((moduleStalkFunctor Y (f x)).map a) ≫
            (δ N).hom =
          (δ M).hom ≫ (moduleStalkFunctor X x).map
            (SheafOfModules.changeOfRingsHom.{u, u, u} α
              (TopCat.Sheaf.inverseImageModule f Y.sheaf M)
              (TopCat.Sheaf.inverseImageModuleMap f Y.sheaf M a)) := by
      apply ModuleCat.ExtendScalars.hom_ext
      intro m
      change (τ _).hom ((β N).hom
        ((ModuleCat.extendScalars ρ).map ((moduleStalkFunctor Y (f x)).map a)
          (@TensorProduct.tmul _ _ _ _ _ _ (Module.compHom _ ρ) _
            (1 : X.presheaf.stalk x) m))) = _
      rw [ModuleCat.ExtendScalars.map_tmul, hβ, hc]
      change (τ _).hom _ = (moduleStalkFunctor X x).map _
        ((τ _).hom ((β M).hom (@TensorProduct.tmul _ _ _ _ _ _ (Module.compHom _ ρ) _
            (1 : X.presheaf.stalk x) m)))
      rw [hβ]
      exact (hτ _ _ (TopCat.Sheaf.inverseImageModuleMap f Y.sheaf M a) 1 (c M m)).symm
    let e : moduleStalkFunctor Y (f x) ⋙ ModuleCat.extendScalars ρ ≅
        P ⋙ moduleStalkFunctor X x := NatIso.ofComponents
      (fun M ↦ δ M ≪≫ ((moduleStalkFunctor X x).mapIso (eqToIso (h M))).symm)
      (by
        intro M N a
        change (ModuleCat.extendScalars ρ).map ((moduleStalkFunctor Y (f x)).map a) ≫
          ((δ N).hom ≫ (moduleStalkFunctor X x).map (eqToHom (h N).symm)) =
          ((δ M).hom ≫ (moduleStalkFunctor X x).map (eqToHom (h M).symm)) ≫
            (moduleStalkFunctor X x).map (P.map a)
        rw [hm a]
        simp only [Functor.map_comp, Category.assoc]
        apply (cancel_mono ((moduleStalkFunctor X x).map (eqToHom (h N)))).1
        simp only [Category.assoc, ← Functor.map_comp, eqToHom_trans,
          eqToHom_refl, Category.comp_id]
        rw [(moduleStalkFunctor X x).map_id]
        simp only [Category.comp_id]
        simpa only [← Category.assoc, ← Functor.map_comp, eqToHom_trans,
          eqToHom_refl, Functor.map_id, Category.id_comp, Category.comp_id] using hδ M N a)
    exact preservesFiniteLimits_of_natIso e
  intro M N a
  let (x : X) := stalkPreserves x
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit (parallelPair a 0))
  apply (stalk_jointlyReflectIsomorphisms X).jointlyReflectsLimit
  intro x
  exact isLimitOfPreserves (P ⋙ moduleStalkFunctor X x) (limit.isLimit _)

end AlgebraicGeometry.RingedSpace
