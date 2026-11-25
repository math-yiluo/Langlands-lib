/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.KoszulOpenConeComparison
import WeilConjectures.AlgebraicGeometry.AffinePerfectKoszulPrincipalUnit

@[expose] public section
universe uMain wMain
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem boundary_zero (A : Type uMain) [CommRing A] (r : ℕ)
    (g : Fin r → A) :
    (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap.comp
      (ExteriorAlgebra.koszulBoundary A r g 0) =
      (Finsupp.linearCombination A g).comp
        (exteriorPower.oneEquiv A (Fin r →₀ A)).toLinearMap := by
  apply exteriorPower.linearMap_ext
  ext v
  change (exteriorPower.zeroEquiv A (Fin r →₀ A))
      (ExteriorAlgebra.koszulBoundary A r g 0 (exteriorPower.ιMulti A 1 v)) = _
  have hb : ExteriorAlgebra.koszulBoundary A r g 0 (exteriorPower.ιMulti A 1 v) =
      (Finsupp.linearCombination A g (v 0)) •
        exteriorPower.ιMulti A 0 (fun i ↦ Fin.elim0 i) := by
    apply Subtype.ext
    simp [ExteriorAlgebra.koszulBoundary, LinearMap.codRestrict_apply,
      ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
      CliffordAlgebra.contractLeft_ι, Algebra.algebraMap_eq_smul_one]
  rw [hb]
  simp


private theorem chain_augmentation_compatibility
    (A : Type uMain) [CommRing A] (r : ℕ) (f : Fin r → A)
    (a b : ℕ) (h : a ≤ b) :
    koszulOpenTransition A r f a b h ≫ koszulOpenAugmentation A r f a =
      koszulOpenAugmentation A r f b := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  change (koszulOpenTransition A r f a b h).f 0 ≫
      (koszulOpenAugmentation A r f a).f 0 = (koszulOpenAugmentation A r f b).f 0
  simp only [koszulOpenAugmentation, ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
  apply ModuleCat.hom_ext
  change ((exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap.comp
    (ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (a + 1)) 0)).comp
      (exteriorPower.map 1 (koszulOpenDiagonal A r f (b - a))) =
    (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap.comp
      (ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (b + 1)) 0)
  rw [boundary_zero, boundary_zero, LinearMap.comp_assoc,
    exteriorPower.oneEquiv_naturality, ← LinearMap.comp_assoc]
  congr 1
  ext i
  simp [koszulOpenDiagonal, Finsupp.linearCombination_single,
    ← pow_add, show b - a + (a + 1) = b + 1 by omega]

/-- Intermediate finite Koszul structural facts; source Tags 08CX and 08DC.
(blueprint: lem-sc-affine-perfect-open-represent-cohomology-core) -/
theorem affine_perfect_open_represent_cohomology_core
    (A : Type uMain) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))] :
    (∀ e : ℕ, ∃ δ : koszulOpenKoszulObject A r f e ⟶
      (koszulOpenObject A r f e)⟦(1 : ℤ)⟧,
      Triangle.mk (koszulOpenUnit A r f e) (koszulOpenKoszulUnit A r f e) δ ∈
        distTriang (schemeDerivedCategory (Spec (.of A)))) ∧
    (∀ e : ℕ, Scheme.IsPerfect (Spec (.of A)) (koszulOpenObject A r f e)) ∧
    (∀ (a b : ℕ) (h : a ≤ b),
      koszulOpenMap A r f a b h ≫ koszulOpenUnit A r f a = koszulOpenUnit A r f b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    obtain ⟨c₀, hc₀⟩ := koszulOpen_module_cone_comparison A r f e
    let u₀ := HomologicalComplex.extendMap (koszulOpenAugmentation A r f e)
      ComplexShape.embeddingDownNat
    let F := (koszulOpenTilde A).mapHomologicalComplex (ComplexShape.up ℤ)
    let c := (CochainComplex.mappingCone.mapHomologicalComplexIso
      u₀ (koszulOpenTilde A)).symm ≪≫ F.mapIso c₀
    have hc : CochainComplex.mappingCone.inr (F.map u₀) ≫ c.hom =
        F.map (HomologicalComplex.extendMap (koszulOpenKoszulInclusion A r f e)
          ComplexShape.embeddingDownNat) := by
      dsimp only [c, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
      rw [← Category.assoc]
      rw [← CochainComplex.mappingCone.map_inr]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Functor.map_comp, hc₀]
    let u := ((koszulOpenTilde A).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap (koszulOpenAugmentation A r f e)
        ComplexShape.embeddingDownNat)
    let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle u)
    let cD := DerivedCategory.Q.mapIso c
    refine ⟨cD.inv ≫ T.mor₃, ?_⟩
    have hT := DerivedCategory.mappingCone_triangle_distinguished u
    refine isomorphic_distinguished T hT _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) cD.symm ?_ ?_ ?_)
    · simp only [Triangle.mk_mor₁, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · simp only [Triangle.mk_mor₂, Iso.symm_hom, Iso.refl_hom, Category.id_comp]
      change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map c.inv =
        DerivedCategory.Q.map (CochainComplex.mappingCone.inr u)
      rw [← Functor.map_comp, ← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp [T, cD]
  · intro e
    exact (affine_perfect_koszul_principal_unit A r f (e + 1) (by omega)).1
  · intro a b h
    unfold koszulOpenMap koszulOpenUnit
    rw [← Functor.map_comp, ← Functor.map_comp, ← HomologicalComplex.extendMap_comp,
      chain_augmentation_compatibility]

end AlgebraicGeometry
