/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Finite étale Čech cohomology and filtered colimits

Source: Stacks Project, Cohomology on Sites, Tag 0739, proof of `lemma-colim-works-over-collection`.
(blueprint: lem-weil-pbc-finite-etale-cech-filtered-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

private theorem shortComplexHomologyColimit (I : Type u) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (ShortComplex.homologyFunctor AddCommGrpCat.{u + 1}) := by
  have : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  let L := colim (J := I) (C := AddCommGrpCat.{u + 1})
  have : L.PreservesHomology := inferInstance
  refine ⟨fun {D} ↦ ?_⟩
  let S := (ShortComplex.functorEquivalence I AddCommGrpCat.{u + 1}).inverse.obj D
  let c : Cocone D :=
    { pt := S.map L
      ι :=
        { app := fun i ↦ S.mapNatTrans (colim.ι i)
          naturality := by
            intro i j f
            apply ShortComplex.Hom.ext
            · change S.X₁.map f ≫ colimit.ι S.X₁ j = colimit.ι S.X₁ i
              exact colimit.w S.X₁ f
            · change S.X₂.map f ≫ colimit.ι S.X₂ j = colimit.ι S.X₂ i
              exact colimit.w S.X₂ f
            · change S.X₃.map f ≫ colimit.ι S.X₃ j = colimit.ι S.X₃ i
              exact colimit.w S.X₃ f } }
  have hc : IsColimit c := ShortComplex.isColimitOfIsColimitπ c
    (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)
  apply preservesColimit_of_preserves_colimit_cocone hc
  let e : D ⋙ ShortComplex.homologyFunctor _ ≅ S.homology :=
    NatIso.ofComponents (fun i ↦ S.mapHomologyIso ((CategoryTheory.evaluation _ _).obj i)) (by
      intro i j f
      change ShortComplex.homologyMap
        (S.mapNatTrans ((CategoryTheory.evaluation _ _).map f)) ≫ _ = _
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp)
  have h : IsColimit ((Cocone.precompose e.hom).obj (colimit.cocone S.homology)) :=
    (IsColimit.precomposeInvEquiv e.symm _).symm (colimit.isColimit _)
  apply IsColimit.ofIsoColimit h
  refine Cocone.ext (S.mapHomologyIso L).symm ?_
  intro i
  change e.hom.app i ≫ colimit.ι S.homology i ≫ (S.mapHomologyIso L).inv =
    ShortComplex.homologyMap (S.mapNatTrans (colim.ι i))
  rw [ShortComplex.homologyMap_mapNatTrans]
  rfl

private theorem complexHomologyColimit (I : Type u) [SmallCategory I] [IsFiltered I]
    (h : PreservesColimitsOfShape I (ShortComplex.homologyFunctor AddCommGrpCat.{u + 1}))
    (p : ℕ) :
    PreservesColimitsOfShape I
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) p) := by
  let H := HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u + 1}
    (ComplexShape.up ℕ) p
  have : PreservesColimitsOfShape I H :=
    ⟨fun {D} ↦ ⟨fun {c} hc ↦ ⟨ShortComplex.isColimitOfIsColimitπ (H.mapCocone c)
      (isColimitOfPreserves
        (HomologicalComplex.eval _ (ComplexShape.up ℕ) ((ComplexShape.up ℕ).prev p)) hc)
      (isColimitOfPreserves (HomologicalComplex.eval _ (ComplexShape.up ℕ) p) hc)
      (isColimitOfPreserves
        (HomologicalComplex.eval _ (ComplexShape.up ℕ) ((ComplexShape.up ℕ).next p)) hc)⟩⟩⟩
  have := h
  change PreservesColimitsOfShape I (H ⋙ ShortComplex.homologyFunctor _)
  infer_instance

private theorem finiteEtaleCechComplexColimit (X : Scheme.{u}) (U : X.Etale)
    (K : Type (u + 1)) [Finite K]
    (V : K → X.Etale) (f : ∀ k : K, V k ⟶ U)
    (I : Type u) [SmallCategory I] [IsFiltered I]
    (hsections : ∀ (q : ℕ) (a : Fin (q + 1) → K),
      PreservesColimitsOfShape I
        ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (op (piObj (fun j : Fin (q + 1) ↦ Over.mk (f (a j)))).left))) :
    PreservesColimitsOfShape I
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft (Over U)ᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (Over.forget U).op ⋙
        cechComplexFunctor (fun k : K ↦ Over.mk (f k))) := by
  let C := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft (Over U)ᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
      (Over.forget U).op ⋙
    cechComplexFunctor (fun k : K ↦ Over.mk (f k))
  apply HomologicalComplex.preservesColimitsOfShape_of_eval C
  intro q
  let A := Fin (q + 1) → K
  let G : Discrete A ⥤ X.Etaleᵒᵖ := Discrete.functor fun a ↦
    op (piObj (fun j : Fin (q + 1) ↦ Over.mk (f (a j)))).left
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft (Discrete A) X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj G
  have : PreservesColimitsOfShape I E :=
    preservesColimitsOfShape_of_evaluation E I (fun a ↦ by
      exact hsections q a.as)
  have : HasFiniteBiproducts AddCommGrpCat.{u + 1} := Abelian.hasFiniteBiproducts
  have : PreservesColimitsOfShape I
      (lim (J := Discrete A) (C := AddCommGrpCat.{u + 1})) :=
    preservesColimitsOfShape_of_natIso (HasBiproductsOfShape.colimIsoLim (J := A))
  let e : C ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) q ≅ E ⋙ lim :=
    NatIso.ofComponents (fun F ↦ Pi.isoLimit (E.obj F)) (by
      intro F F' φ
      apply limit.hom_ext
      intro a
      simp only [Functor.comp_obj, HomologicalComplex.eval_obj, lim_obj, Functor.comp_map,
        HomologicalComplex.eval_map, Category.assoc, lim_map, limMap_π]
      change (CategoryTheory.Limits.Pi.map (fun a : A ↦ φ.hom.app (G.obj ⟨a⟩))) ≫ _ = _
      simp [G, E, Pi.isoLimit])
  exact preservesColimitsOfShape_of_natIso e.symm

/-- If sections on every member of a finite Čech nerve preserve filtered colimits,
then its Čech cohomology functors preserve those colimits, in every degree.
Source: Stacks Project, Tag 0739, proof of `lemma-colim-works-over-collection`,
the finite-cover Čech step.
(blueprint: lem-weil-pbc-finite-etale-cech-filtered-colimit).

Proof:
1. In degree `q`, the Čech complex is the product of evaluation at the objects
   `piObj (fun j : Fin (q + 1) ↦ Over.mk (f (a j)))`, indexed by
   `a : Fin (q + 1) → K`. This index type is finite, including when `K` is empty.
2. The hypothesis identifies each factor of the image cocone with a colimit.
   Filtered colimits in abelian groups commute with finite products (finite products
   are finite biproducts). Thus the image cocone is a colimit in every degree.
   The component comparison maps commute with each restriction along a face map,
   by naturality of the original cocone; hence they commute with the alternating
   sums defining the differential. Degreewise colimits are colimits of complexes.
3. Filtered colimits of abelian groups are exact. Applied to the kernels and images
   of the differentials this identifies the homology of the colimit complex with
   the colimit of the homology groups. Composing with step 2 gives preservation
   by the displayed Čech cohomology functor, with its original cocone legs. -/
theorem preservesColimitsOfShape_finiteEtaleCechHomology
    (X : Scheme.{u}) (U : X.Etale) (K : Type (u + 1)) [Finite K]
    (V : K → X.Etale) (f : ∀ k : K, V k ⟶ U)
    (I : Type u) [SmallCategory I] [IsFiltered I]
    (hsections : ∀ (q : ℕ) (a : Fin (q + 1) → K),
      PreservesColimitsOfShape I
        ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (op (piObj (fun j : Fin (q + 1) ↦ Over.mk (f (a j)))).left)))
    (p : ℕ) :
    PreservesColimitsOfShape I
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft (Over U)ᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (Over.forget U).op ⋙
        cechComplexFunctor (fun k : K ↦ Over.mk (f k)) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) p) := by
  let C := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft (Over U)ᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
      (Over.forget U).op ⋙ cechComplexFunctor (fun k : K ↦ Over.mk (f k))
  have : PreservesColimitsOfShape I C :=
    finiteEtaleCechComplexColimit X U K V f I hsections
  have := complexHomologyColimit I (shortComplexHomologyColimit I) p
  have h : PreservesColimitsOfShape I
      (C ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p) := inferInstance
  simpa only [C, Functor.assoc] using h

end AlgebraicGeometry.Scheme
