/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.HypercohomologyLeftEdge

/-! # Naturality of the hypercohomology left edge

Source: Stacks Project, derived.tex, Tag 015J.
-/

@[expose] public section

universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]

/-- Naturality of the complex hypercohomology left edge.
Source: Stacks Project, derived.tex, Tag 015J, functoriality of the second spectral sequence.
(blueprint: lem-pc-hypercohomology-left-edge-naturality)

Proof: extend the cochain map by zero. Naturality of the extension homology isomorphism,
the map-extension isomorphism and the quotient homology isomorphism transports its ordinary
homology map to the derived-category homology map. Naturality of the derived unit then
moves the map through the unit. Apply naturality of the first-quadrant spectral object's
left edge and of the truncation/shift/degree-zero target comparison. Finally apply the
quotient and extension homology naturality equations on the target. Associate the composites;
this is the stated equality. All maps are defined also in degree zero, so no positivity
assumption on n is used. -/
theorem cochainHypercohomologyLeftEdge_naturality
    {K L : CochainComplex B ℕ} (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map f) n ≫
      G.cochainHypercohomologyLeftEdge L n =
    G.cochainHypercohomologyLeftEdge K n ≫ G.map (HomologicalComplex.homologyMap f n) := by
  let e := ComplexShape.embeddingUpNat
  let K' : CochainComplex.Plus B := ⟨K.extend e, 0, inferInstance⟩
  let L' : CochainComplex.Plus B := ⟨L.extend e, 0, inferInstance⟩
  let f' : K' ⟶ L' := ObjectProperty.homMk (HomologicalComplex.extendMap f e)
  let GK := G.mapCochainComplexPlus.obj K'
  let GL := G.mapCochainComplexPlus.obj L'
  let Gf := G.mapCochainComplexPlus.map f'
  let H := DerivedCategory.Plus.homologyFunctor C n
  have hK : DerivedCategory.Plus.TStructure.t.IsGE (DerivedCategory.Plus.Q.obj K') 0 := by
    apply (DerivedCategory.Plus.isGE_ι_obj_iff _ 0).mp
    exact inferInstanceAs ((DerivedCategory.Q.obj K'.obj).IsGE 0)
  have hL : DerivedCategory.Plus.TStructure.t.IsGE (DerivedCategory.Plus.Q.obj L') 0 := by
    apply (DerivedCategory.Plus.isGE_ι_obj_iff _ 0).mp
    exact inferInstanceAs ((DerivedCategory.Q.obj L'.obj).IsGE 0)
  let EK := ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendHomologyIso e
    (rfl : (n : ℤ) = n)
  let EL := ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).extendHomologyIso e
    (rfl : (n : ℤ) = n)
  let mK := K.mapExtendIso e G
  let mL := L.mapExtendIso e G
  have hex :
      HomologicalComplex.homologyMap
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map f) n ≫ EL.inv =
        EK.inv ≫ HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap
            ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map f) e) (n : ℤ) := by
    apply (cancel_epi EK.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← HomologicalComplex.extendHomologyIso_hom_naturality]
    simp only [EL, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hm :
      HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap
            ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map f) e) (n : ℤ) ≫
        HomologicalComplex.homologyMap mL.inv (n : ℤ) =
      HomologicalComplex.homologyMap mK.inv (n : ℤ) ≫
        HomologicalComplex.homologyMap Gf.hom (n : ℤ) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    congr 1
    exact (e.mapExtendFunctorNatIso G).inv.naturality f
  have hq :
      HomologicalComplex.homologyMap Gf.hom (n : ℤ) ≫
          (DerivedCategory.Plus.homologyFunctorObjQIso GL n).inv =
        (DerivedCategory.Plus.homologyFunctorObjQIso GK n).inv ≫
          H.map (DerivedCategory.Plus.Q.map Gf) := by
    apply (cancel_mono (DerivedCategory.Plus.homologyFunctorObjQIso GL n).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hu := G.rightDerivedFunctorPlusUnit.naturality f'
  have he := Abelian.SpectralObject.leftEdge_naturality
    (G.hypercohomologySpectralObjectFunctor.map (DerivedCategory.Plus.Q.map f')) (n : ℤ)
  have ht := (G.hypercohomologyLeftEdgeTargetIso n).hom.naturality
    (DerivedCategory.Plus.Q.map f')
  simp only [cochainHypercohomologyLeftEdge, Category.assoc]
  rw [reassoc_of% hex, reassoc_of% hm, reassoc_of% hq]
  have hu' := congrArg H.map hu
  simp only [Functor.map_comp] at hu'
  erw [reassoc_of% hu']
  erw [reassoc_of% he, reassoc_of% ht]
  simp only [G.map_comp, Category.assoc]
  rw [← G.map_comp_assoc, ← G.map_comp]
  erw [DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality]
  dsimp only [f', ObjectProperty.homMk_hom]
  rw [Category.assoc]
  erw [HomologicalComplex.extendHomologyIso_hom_naturality]
  simp only [G.map_comp]
  rfl

end CategoryTheory.Functor
