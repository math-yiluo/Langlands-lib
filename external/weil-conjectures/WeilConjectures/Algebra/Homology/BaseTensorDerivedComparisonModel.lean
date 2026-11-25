/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseTensorDerivedComparison

/-! # Evaluation of the derived coefficient comparison on a cohomology model

Source: Stacks Project, Tags 06Y6 and 0DJ7.
(blueprint: lem-pc-base-tensor-derived-comparison-model).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ModuleCat

variable (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} D)]

/-- Identify the adjoint transpose of one model's comparison with the derived
coefficient transformation. This is a computation at one complex, with no
morphism between complexes or derived objects.

Proof: form beta as ordinaryIso followed by restriction of ordinaryToLocalized.
Their generator equations give the coefficient-map formula in
IsBaseTensorDerivedComparison. Apply its representative equation. Substitute
comparison_eq and localized_eq. The two successive
restriction-of-scalars homology isomorphisms are written separately in the
representative equation. Naturality of the B-restriction homology isomorphism
identifies the homology of beta with restriction of the composite comparison
and ordinaryToLocalized. The counit compatibility
of zeta identifies the derived counit on the right with the model counit.
Naturality of zeta with the input localization isomorphism moves its component
to the derived restricted input. This gives the equation after composing both
sides with restriction of s.hom. Cancel that invertible map to get the formula
with s.inv. Tensor induction proves each chain-map identification, so there is
no choice of associativity or coefficient maps and no flatness assumption.
Source: Stacks Project, Tag 06Y6 and equation-bc (Tag 0DJ7).
(blueprint: lem-pc-base-tensor-derived-comparison-model). -/
theorem baseTensorDerivedComparison_model
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (δ : DerivedCategory.Qh ⋙ F ⟶
      (extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (L : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} D))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
        (algebraMap A (A ⊗[R] B)))).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (i : ℤ)
    (τ : (restrictScalars.{u} (algebraMap R A)).mapDerivedCategory ⋙ F ⋙
        DerivedCategory.homologyFunctor _ i ⟶
      L ⋙ DerivedCategory.homologyFunctor _ i ⋙
        restrictScalars.{u} (algebraMap (A ⊗[R] B) D) ⋙
          restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom)
    (hτ : IsBaseTensorDerivedComparison R A B D F δ L ε i τ)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : BaseDerivedTensorCohomologyModel R A B P D)
    (ζ : M.derived ≅ F)
    (hζ : Functor.whiskerLeft DerivedCategory.Qh ζ.hom ≫ δ = M.counit)
    (s : (DerivedCategory.homologyFunctor _ i).obj (L.obj (DerivedCategory.Q.obj P)) ≅
      (((extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
        (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj P).homology i)
    (hs : s.hom = scalarExtensionHomologyMap _ L ε P i) :
    (restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map
      ((extendRestrictScalarsAdj.{u, u, u} (algebraMap (A ⊗[R] B) D)).unit.app
        (M.cohomology i) ≫
          (restrictScalars.{u} (algebraMap (A ⊗[R] B) D)).map
            (M.localizedComparison i ≫ s.inv)) =
    (M.cohomologyIso i).hom ≫ (DerivedCategory.homologyFunctor _ i).map
      (M.derived.map (((DerivedCategory.quotientCompQhIso _).app _ ≪≫
        (restrictScalars.{u} (algebraMap R A)).mapDerivedCategoryFactors.symm.app P).hom) ≫
        (ζ.app ((restrictScalars.{u} (algebraMap R A)).mapDerivedCategory.obj
          (DerivedCategory.Q.obj P))).hom) ≫ τ.app (DerivedCategory.Q.obj P) := by
  let E := A ⊗[R] B
  let r := restrictScalars.{u}
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  let t := restrictScalars.{u} (algebraMap E D)
  let c := ((extendScalars.{u, u, u} ((algebraMap E D).comp
    (algebraMap A E))).mapHomologicalComplex (.up ℤ)).obj P
  let β := M.ordinaryIso.hom ≫
    (r.mapHomologicalComplex (.up ℤ)).map M.ordinaryToLocalized
  have hβ : ∀ (j : ℤ) (b : B) (p : P.X j),
      β.f j (b ⊗ₜ[R, algebraMap R B] p) =
        (algebraMap E D (Algebra.TensorProduct.includeRight b) ⊗ₜ[A,
          (algebraMap E D).comp (algebraMap A E)] p) := by
    intro j b p
    change M.ordinaryToLocalized.f j
      (M.ordinaryIso.hom.f j (b ⊗ₜ[R, algebraMap R B] p)) = _
    rw [M.ordinaryIso_tmul, M.ordinaryToLocalized_tmul]
  have hp := hτ P β hβ
  apply (cancel_mono ((t ⋙ r).map s.hom)).1
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  change r.map _ ≫ r.map (t.map _) ≫ r.map (t.map s.inv) ≫ r.map (t.map s.hom) = _
  rw [← r.map_comp, ← t.map_comp, s.inv_hom_id, t.map_id, r.map_id,
    Category.comp_id, ← r.map_comp, M.localized_eq]
  simp only [Functor.map_comp]
  simp only [Functor.comp_map] at hp
  rw [hs, ← hp]
  let k := (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    (restrictScalars.{u} (algebraMap R A)).mapDerivedCategoryFactors.symm.app P
  have hk : M.derived.map k.hom ≫ ζ.hom.app _ ≫
      (F.map k.inv ≫ δ.app _) = M.counit.app _ := by
    rw [← ζ.hom.naturality_assoc k.inv]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
    rw [M.derived.map_id, Category.id_comp]
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj] using
      congrArg (fun η ↦ η.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj P))) hζ
  change r.map (M.comparison i) ≫ r.map (HomologicalComplex.homologyMap
    M.ordinaryToLocalized i) ≫ r.map (((c.sc i).mapHomologyIso t).hom) =
    (M.cohomologyIso i).hom ≫ (DerivedCategory.homologyFunctor _ i).map
      (M.derived.map k.hom) ≫ (DerivedCategory.homologyFunctor _ i).map
        (ζ.hom.app _) ≫ (DerivedCategory.homologyFunctor _ i).map
          (F.map k.inv ≫ δ.app _) ≫ _
  rw [← (DerivedCategory.homologyFunctor _ i).map_comp_assoc,
    ← (DerivedCategory.homologyFunctor _ i).map_comp_assoc]
  simp only [Category.assoc]
  rw [hk]
  dsimp only [β]
  rw [HomologicalComplex.homologyMap_comp]
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ i).map M.ordinaryToLocalized) r
  change HomologicalComplex.homologyMap
      ((r.mapHomologicalComplex (.up ℤ)).map M.ordinaryToLocalized) i ≫
      (((t.mapHomologicalComplex (.up ℤ)).obj c).sc i |>.mapHomologyIso r).hom =
    _ at hn
  simp only [Category.assoc]
  have hn' := congrArg (fun f ↦ f ≫ r.map (((c.sc i).mapHomologyIso t).hom)) hn
  simp only [Category.assoc] at hn'
  rw [hn']
  simp only [← Category.assoc]
  erw [← M.comparison_eq i]
  simp only [Category.assoc]
  let j := ((((extendScalars.{u, u, u} (algebraMap A E)).mapHomologicalComplex
    (.up ℤ)).obj P).sc i).mapHomologyIso r
  change r.map (M.comparison i) ≫ r.map (HomologicalComplex.homologyMap
    M.ordinaryToLocalized i) ≫ r.map (((c.sc i).mapHomologyIso t).hom) =
    r.map (M.comparison i) ≫ j.inv ≫ j.hom ≫
      r.map (HomologicalComplex.homologyMap M.ordinaryToLocalized i) ≫
        r.map (((c.sc i).mapHomologyIso t).hom)
  rw [j.inv_hom_id_assoc]

end ModuleCat
