/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeCocycleCoordinates
public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import WeilConjectures.CategoryTheory.Abelian.FirstResolutionExtensionClass

/-!
# Ordinary normalization of framed relative classes

## References

* Stacks Project, Tag 03AJ
* Tags 06XR and 06XV
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Forgetting the open lift identifies the framed cocycle with the negative extension class. -/
theorem relativeFrameClass_forget
    (T : Scheme.{u}) (U : T.Etale)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (I : InjectiveResolution G)
    (c : ResolutionSectionCanonicalComparison G I) (z : ResolutionFramedLift T U I) :
    c.globalEquiv 1
      (((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).extendHomologyIso ComplexShape.embeddingUpNat (rfl : (1 : ℤ) = 1)).hom
          (HomologicalComplex.homologyMap (relativeForgetComplex T U I.cocomplex) 1
            (relativeFrameClass T U I z))) =
      -Sheaf.H.δSections (resolutionLiftSequence_shortExact T I)
        (MorphismProperty.Over.mkIdTerminal @Etale T) z.1 := by
  rw [relativeFrameAbsoluteCycle_class]
  let hT := MorphismProperty.Over.mkIdTerminal @Etale T
  let η (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1} hT).homAddEquiv _ F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  have hη {F F' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
      (k : F ⟶ F') (b : (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶ F) :
      η F' (b ≫ k) = k.hom.app (op (Scheme.Etale.mk (𝟙 T))) (η F b) := by
    dsimp only [η, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
    rw [Adjunction.homEquiv_naturality_right]
    rfl
  let g := (η (I.cocomplex.cycles 1)).symm z.1
  let f := g ≫ I.cocomplex.iCycles 1
  have hf : f ≫ I.cocomplex.d 1 2 = 0 := by simp [f, Category.assoc]
  have hrep :
      ((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).iCycles 1) (relativeFrameAbsoluteCycle T U I z) =
      η (I.cocomplex.X 1) f := by
    rw [relativeFrameAbsoluteCycle_i, hη]
    simp only [g, AddEquiv.apply_symm_apply]
  rw [c.global_cocycle 1 f hf _ hrep]
  dsimp only [f]
  rw [← InjectiveResolution.mk₀_comp_extMk, InjectiveResolution.extMk_firstCycles
    I _ (resolutionLiftSequence_shortExact T I), Abelian.Ext.comp_neg, Sheaf.H.δ_apply]
  · congr 2
  · simp

end AlgebraicGeometry.Etale

-- Check the axioms of the completed construction.
