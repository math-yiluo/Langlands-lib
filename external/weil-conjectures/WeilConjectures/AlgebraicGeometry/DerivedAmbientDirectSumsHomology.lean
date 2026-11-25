/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Exact colimits commute with homology of short complexes. The proof follows the
functor-category comparison used by `FiniteEtaleCechFilteredColimit`. -/
private theorem shortComplexHomologyColimit
    (C : Type*) [Category* C] [Abelian C]
    (I : Type u) [SmallCategory I] [HasColimitsOfShape I C]
    [HasExactColimitsOfShape I C] :
    PreservesColimitsOfShape I (ShortComplex.homologyFunctor C) := by
  let L := colim (J := I) (C := C)
  have : L.PreservesHomology := inferInstance
  refine ⟨fun {D} ↦ ?_⟩
  let S := (ShortComplex.functorEquivalence I C).inverse.obj D
  let c : Cocone D :=
    { pt := S.map L
      ι :=
        { app := fun i ↦ S.mapNatTrans (colim.ι i)
          naturality := by
            intro i j f
            apply ShortComplex.Hom.ext
            · simpa [S, L, ShortComplex.functorEquivalence,
                ShortComplex.FunctorEquivalence.inverse, ShortComplex.mapNatTrans]
                using colimit.w (D ⋙ ShortComplex.π₁) f
            · simpa [S, L, ShortComplex.functorEquivalence,
                ShortComplex.FunctorEquivalence.inverse, ShortComplex.mapNatTrans]
                using colimit.w (D ⋙ ShortComplex.π₂) f
            · simpa [S, L, ShortComplex.functorEquivalence,
                ShortComplex.FunctorEquivalence.inverse, ShortComplex.mapNatTrans]
                using colimit.w (D ⋙ ShortComplex.π₃) f } }
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
  dsimp only [Functor.mapCocone, c, Cocone.precompose, colimit.cocone,
    Cocone.functoriality, NatTrans.comp_app, Iso.symm_hom, ShortComplex.homologyFunctor_map]
  rw [Category.assoc]
  change e.hom.app i ≫ colimit.ι S.homology i ≫ (S.mapHomologyIso L).inv =
    ShortComplex.homologyMap (S.mapNatTrans (colim.ι i))
  rw [ShortComplex.homologyMap_mapNatTrans]
  rfl

/-- Reduce complex homology to the three-term short complex in the given degree. -/
private theorem complexHomologyColimit
    (C : Type*) [Category* C] [Abelian C]
    (I : Type u) [SmallCategory I] [HasColimitsOfShape I C]
    (h : PreservesColimitsOfShape I (ShortComplex.homologyFunctor C))
    (p : ℤ) :
    PreservesColimitsOfShape I
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) p) := by
  let H := HomologicalComplex.shortComplexFunctor C
    (ComplexShape.up ℤ) p
  have : PreservesColimitsOfShape I H :=
    ⟨fun {D} ↦ ⟨fun {c} hc ↦ ⟨ShortComplex.isColimitOfIsColimitπ (H.mapCocone c)
      (isColimitOfPreserves
        (HomologicalComplex.eval _ (ComplexShape.up ℤ) ((ComplexShape.up ℤ).prev p)) hc)
      (isColimitOfPreserves (HomologicalComplex.eval _ (ComplexShape.up ℤ) p) hc)
      (isColimitOfPreserves
        (HomologicalComplex.eval _ (ComplexShape.up ℤ) ((ComplexShape.up ℤ).next p)) hc)⟩⟩⟩
  have := h
  change PreservesColimitsOfShape I (H ⋙ ShortComplex.homologyFunctor _)
  infer_instance

local instance instHasColimitsOfShape_derivedAmbientDirectSumsHomology
    (X : Scheme.{u}) (I : Type u) :
    HasColimitsOfShape (Discrete I)
      (CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  have : HasColimitsOfShape (Discrete I) C := inferInstance
  refine ⟨fun F ↦ ?_⟩
  have (n : ℤ) : HasColimit (F ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
    HasColimitsOfShape.has_colimit _
  exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩

/-- Cohomology of a termwise coproduct is the coproduct of the cohomologies, with the
canonical map induced by the coprojections.
Source: Stacks Project, Derived Categories of Schemes, proof of Lemma 08DT.
(blueprint: lem-pc-derived-ambient-direct-sums-homology)

Proof: Coproducts of module sheaves are exact. Apply the exact colimit functor to
short complexes and use its homology comparison isomorphism; evaluation at the three
terms shows this is the colimit of the diagram of short complexes. The short complex
in degrees q-1, q, q+1 of a cochain complex is also computed termwise, so its homology
functor preserves coproducts. The natural isomorphism identifying homology after Q
with complex homology transfers this preservation to Q followed by derived homology.
Thus the comparison map induced by Q of the coprojections is invertible. The map in
the statement is its composite with the coproduct of homology of e(i).inv, which is
also invertible. This applies to the empty family and to every integer degree. -/
theorem derivedAmbientDirectSumsHomology (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (I : Type u) (E : I → schemeDerivedCategory X)
    (K : I → CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (e : ∀ i : I, DerivedCategory.Q.obj (K i) ≅ E i) (q : ℤ) :
    IsIso (Sigma.desc (fun i ↦
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) q).map
          ((e i).inv ≫ DerivedCategory.Q.map (Sigma.ι K i)))) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  have : IsGrothendieckAbelian.{u} C :=
    SheafOfModules.isGrothendieckAbelian _
  have h := shortComplexHomologyColimit C (Discrete I)
  have := complexHomologyColimit C (Discrete I) h q
  have : PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor C q) :=
    preservesColimitsOfShape_of_natIso (DerivedCategory.homologyFunctorFactors C q).symm
  let H := DerivedCategory.homologyFunctor C q
  have : IsIso (Sigma.desc (fun i ↦ H.map (DerivedCategory.Q.map (Sigma.ι K i)))) := by
    exact inferInstanceAs (IsIso (sigmaComparison (DerivedCategory.Q ⋙ H) K))
  have : IsIso (Limits.Sigma.map (fun i ↦ H.map (e i).inv)) := by infer_instance
  have heq : Sigma.desc (fun i ↦ H.map
      ((e i).inv ≫ DerivedCategory.Q.map (Sigma.ι K i))) =
      Limits.Sigma.map (fun i ↦ H.map (e i).inv) ≫
        Sigma.desc (fun i ↦ H.map (DerivedCategory.Q.map (Sigma.ι K i))) := by
    ext i
    simp [Functor.map_comp]
  rw [heq]
  infer_instance

end AlgebraicGeometry
