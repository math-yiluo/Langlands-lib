/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.CanonicalSymmetricGradedAlgebra
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality

set_option linter.privateModule false

/-! # Epimorphy of the quotient of an arbitrary normalized projective-bundle realization
The local argument follows SymmetricProjNormalizedQuotientEpi, transporting its generators
by the realization section equivalence.

## References

* Stacks Project, Constructions, Tags 01OB and 01O4
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomogeneousLocalization
namespace AlgebraicGeometry
open Scheme.Modules
attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  projectiveBundlePullbackAdjunction projectiveBundlePullbackSection
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι

private theorem tensor_unit_injective {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) (V : Y.Opens) (hV : V ≤ j.opensRange) :
    Function.Injective (((projectiveBundlePullbackAdjunction j).unit.app M).app V) := by
  let a := projectiveBundlePullbackAdjunction j
  let b := pullbackPushforwardAdjunction j
  have h := a.unit_leftAdjointUniq_hom_app b M
  have hi := (bijective_pullbackUnit_app_of_isOpenImmersion j M hV).injective
  intro s t hst
  apply hi
  have hs := congrArg (fun f ↦ f.app V s) h
  have ht := congrArg (fun f ↦ f.app V t) h
  change _ = (pullbackUnit j M).app V s at hs
  change _ = (pullbackUnit j M).app V t at ht
  rw [← hs, ← ht]
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app]
  exact congrArg _ hst

private theorem zero_of_tensor_open_cover {X : Scheme.{u}} {I : Type u}
    (Y : I → Scheme.{u}) (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hj : ⨆ i, (j i).opensRange = ⊤) {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ i, (tensorPullback (j i)).map f = 0) : f = 0 := by
  apply hom_ext
  intro V
  ext s
  change f.app V s = 0
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i ↦ V ⊓ (j i).opensRange) V (fun _ ↦ homOfLE inf_le_left)
    (fun x hx ↦ ?_) _ 0 (fun i ↦ ?_)
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hj.ge (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  · rw [map_zero, ← Hom.app_presheaf_map]
    let W := V ⊓ (j i).opensRange
    let t : Γ(M, W) := M.presheaf.map (homOfLE inf_le_left).op s
    apply tensor_unit_injective (j i) N W inf_le_right
    have h := congrArg (fun k ↦ k.app W t)
      ((projectiveBundlePullbackAdjunction (j i)).unit.naturality f)
    change ((projectiveBundlePullbackAdjunction (j i)).unit.app N).app W (f.app W t) =
      ((tensorPullback (j i)).map f).app ((j i) ⁻¹ᵁ W)
        (((projectiveBundlePullbackAdjunction (j i)).unit.app M).app W t) at h
    change ((projectiveBundlePullbackAdjunction (j i)).unit.app N).app W (f.app W t) =
      ((projectiveBundlePullbackAdjunction (j i)).unit.app N).app W 0
    rw [map_zero, h, hf i]
    rfl

private theorem zero_of_twist_generators {R B : Type u} [CommRing R]
    [SetLike B R] [AddSubgroupClass B R] (𝒜 : ℕ → B) [GradedRing 𝒜]
    {I : Type u} (a : I → R) (ha : ∀ i, a i ∈ 𝒜 1)
    (hcover : ⨆ i, Proj.basicOpen 𝒜 (a i) = ⊤)
    {N : (Proj 𝒜).Modules} (g : Proj.twist 𝒜 1 ⟶ N)
    (hg : ∀ i, Proj.unitToTwist (ha i) ≫ g = 0) : g = 0 := by
  apply hom_ext
  intro V
  ext t
  change g.app V t = 0
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i ↦ V ⊓ Proj.basicOpen 𝒜 (a i)) V (fun _ ↦ homOfLE inf_le_left)
    (fun x hx ↦ ?_) _ 0 (fun i ↦ ?_)
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover.ge (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  · rw [map_zero, ← Hom.app_presheaf_map]
    let W := V ⊓ Proj.basicOpen 𝒜 (a i)
    obtain ⟨r, hr⟩ := (Proj.bijective_unitToTwist_app (ha i)
      (V := W) inf_le_right).surjective
      ((Proj.twist 𝒜 1).presheaf.map (homOfLE inf_le_left).op t)
    rw [← hr]
    exact congrArg (fun k ↦ k.app W r) (hg i)

end AlgebraicGeometry
