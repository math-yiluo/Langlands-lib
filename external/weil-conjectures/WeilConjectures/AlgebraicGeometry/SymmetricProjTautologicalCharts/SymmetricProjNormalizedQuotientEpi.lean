/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality

/-! # Epimorphy of the normalized symmetric Proj quotient

Source: Stacks Project, Constructions, Tags 01NR and 01OB.
(blueprint: lem-trf-symmetric-proj-normalized-quotient-epi).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomogeneousLocalization
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

open Scheme.Modules

private theorem tensor_unit_section {X Y : Scheme.{u}} (j : X ⟶ Y)
    (M : Y.Modules) (V : Y.Opens) (s : Γ(M, V)) :
    ((tensorPullbackSectionAdjunction j).unit.app M).app V s =
      tensorPullbackSection j M V s :=
  (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction j)).1 M V s

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionAdjunction Scheme.Modules.tensorPullbackSection
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι

private theorem tensor_unit_injective {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) (V : Y.Opens) (hV : V ≤ j.opensRange) :
    Function.Injective (((tensorPullbackSectionAdjunction j).unit.app M).app V) := by
  let a := tensorPullbackSectionAdjunction j
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
      ((tensorPullbackSectionAdjunction (j i)).unit.naturality f)
    change ((tensorPullbackSectionAdjunction (j i)).unit.app N).app W (f.app W t) =
      ((tensorPullback (j i)).map f).app ((j i) ⁻¹ᵁ W)
        (((tensorPullbackSectionAdjunction (j i)).unit.app M).app W t) at h
    change ((tensorPullbackSectionAdjunction (j i)).unit.app N).app W (f.app W t) =
      ((tensorPullbackSectionAdjunction (j i)).unit.app N).app W 0
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

private theorem symmetric_chart_cover {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    (𝒜 : ℕ → Submodule R (SymmetricAlgebra R M)) [GradedAlgebra 𝒜]
    (hι : ∀ m : M, SymmetricAlgebra.ι R M m ∈ 𝒜 1) :
    (⨆ m : M, Proj.basicOpen 𝒜 (SymmetricAlgebra.ι R M m)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top' 𝒜 (SymmetricAlgebra.ι R M) (fun m ↦ ⟨1, hι m⟩)
  apply top_unique
  intro x hx
  clear hx
  induction x using SymmetricAlgebra.induction with
  | algebraMap r =>
    exact (Algebra.adjoin (𝒜 0) (Set.range (SymmetricAlgebra.ι R M))).algebraMap_mem
      (algebraMap R (𝒜 0) r)
  | ι m => exact Algebra.subset_adjoin ⟨m, rfl⟩
  | mul a b ha hb => exact mul_mem ha hb
  | add a b ha hb => exact add_mem ha hb

/-- The adjoint of a section-normalized map to the degree-one twist is epic.
Source: Stacks, Tags 01OB and 01O4 (lemma-apply-relative).
(blueprint: lem-trf-symmetric-proj-normalized-quotient-epi).

Proof: the standard opens D_+(iota(m)) cover each affine symmetric Proj. Indeed, if a
homogeneous prime contained all iota(m), it would contain the positive-degree ideal,
contradicting the definition of Proj. On D_+(iota(m)), multiplication by iota(m)
trivializes the degree-one twist, with inverse division by iota(m). The assumed
normalization says that the adjoint quotient takes the actual pulled-back section
1 tensor m to this frame. Thus the quotient is surjective there: a target section
is uniquely a scalar times the frame and is lifted by that scalar times 1 tensor m.
Transport across the chart isomorphism and the tensor-pullback composition comparison.
These standard opens over all affine base opens cover the global relative Proj, so
local surjectivity proves the quotient is epic. The argument also covers zero and
nilpotent sections: their standard opens are empty. -/
theorem epi_of_symmetric_twist_sections
    {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
    (L : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules)
    (chart : ∀ U : S.affineOpens,
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)).obj L ≅
          Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) 1)
    (σ : E ⟶ (Scheme.Modules.pushforward
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).obj L)
    (hσ :
    ∀ (U : S.affineOpens) (m : E.val.obj (op U.1))
      (hm : SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m ∈
        (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 1),
    (chart U).hom.app
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
        (Scheme.Modules.tensorPullbackSection
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U) L
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
          (σ.app U.1 m)) =
      Scheme.Modules.Hom.app (Proj.unitToTwist
        (𝒜 := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) hm)
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
        (1 : Γ(Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U),
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)))) :
    Epi (((Scheme.Modules.tensorPullbackSectionAdjunction
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).homEquiv E L).symm σ) := by
  classical
  let A := SymmetricAlgebraSheaf.gradedAlgebraData E
  let p := A.relProjHom
  let adj := tensorPullbackSectionAdjunction p
  apply Preadditive.epi_of_cancel_zero
  intro N f hf
  change (adj.homEquiv E L).symm σ ≫ f = 0 at hf
  have hσf : σ ≫ (pushforward p).map f = 0 := by
    have h := congrArg (adj.homEquiv E N) hf
    rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply] at h
    rw [h, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  apply zero_of_tensor_open_cover
    (fun U : S.affineOpens ↦ Proj (A.grading U)) A.relProjι A.iSup_opensRange_relProjι f
  intro U
  let : GradedAlgebra (A.grading U) := A.gradedAlgebra U
  let j := A.relProjι U
  let g := (chart U).inv ≫ (tensorPullback j).map f
  have htop : j ⁻¹ᵁ (p ⁻¹ᵁ U.1) = ⊤ := by
    rw [A.relProjHom_preimage U]
    exact j.preimage_opensRange
  have hgen (m : E.val.obj (op U.1))
      (hm : SymmetricAlgebra.ι Γ(S, U.1) _ m ∈ A.grading U 1) :
      Proj.unitToTwist hm ≫ g = 0 := by
    apply unit_hom_ext
    change g.app ⊤ ((Proj.unitToTwist hm).app ⊤ (1 : Γ(Proj (A.grading U), ⊤))) = 0
    have hn := hσ U m hm
    have hz : f.app (p ⁻¹ᵁ U.1) (σ.app U.1 m) = 0 := by
      exact congrArg (fun k ↦ k.app U.1 m) hσf
    have hnat := congrArg (fun k ↦ k.app (p ⁻¹ᵁ U.1) (σ.app U.1 m))
      ((tensorPullbackSectionAdjunction j).unit.naturality f)
    simp only [Functor.id_map, Functor.comp_map, Hom.comp_app,
      ConcreteCategory.comp_apply, pushforward_map_app, tensor_unit_section] at hnat
    change tensorPullbackSection j N (p ⁻¹ᵁ U.1)
        (f.app (p ⁻¹ᵁ U.1) (σ.app U.1 m)) =
      ((tensorPullback j).map f).app (j ⁻¹ᵁ (p ⁻¹ᵁ U.1))
        (tensorPullbackSection j L (p ⁻¹ᵁ U.1) (σ.app U.1 m)) at hnat
    rw [hz, ← tensor_unit_section, map_zero] at hnat
    have he : g.app (j ⁻¹ᵁ (p ⁻¹ᵁ U.1))
        ((chart U).hom.app (j ⁻¹ᵁ (p ⁻¹ᵁ U.1))
          (tensorPullbackSection j L (p ⁻¹ᵁ U.1) (σ.app U.1 m))) = 0 := by
      change (((chart U).hom ≫ g).app (j ⁻¹ᵁ (p ⁻¹ᵁ U.1))) _ = 0
      simp only [g, Iso.hom_inv_id_assoc]
      exact hnat.symm
    rw [hn] at he
    change g.app (j ⁻¹ᵁ (p ⁻¹ᵁ U.1))
      ((Proj.unitToTwist hm).app (j ⁻¹ᵁ (p ⁻¹ᵁ U.1))
        (1 : Γ(Proj (A.grading U), j ⁻¹ᵁ (p ⁻¹ᵁ U.1)))) = 0 at he
    rw [htop] at he
    exact he
  have hm (m : E.val.obj (op U.1)) :
      SymmetricAlgebra.ι Γ(S, U.1) _ m ∈ A.grading U 1 := by
    change _ ∈ (SymmetricAlgebra.ι Γ(S, U.1) _).range ^ 1
    simpa only [pow_one] using LinearMap.mem_range_self _ m
  have hg : g = 0 := zero_of_twist_generators (A.grading U)
    (SymmetricAlgebra.ι Γ(S, U.1) _) hm (symmetric_chart_cover (A.grading U) hm) g
    (fun m ↦ hgen m (hm m))
  have h := congrArg ((chart U).hom ≫ ·) hg
  simpa only [g, Iso.hom_inv_id_assoc, comp_zero] using h

end AlgebraicGeometry.SymmetricProjTautologicalCharts
