import Langlands.AlgebraicGeometry.Modules.ClosedImmersionCohomologyResolution
import Langlands.AlgebraicGeometry.Modules.PushforwardCohomologyComposition
import Langlands.Cohomology.AcyclicResolution.ComparisonProof

/-! # Composition of actual closed-immersion cohomology maps -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {Y Z T : Scheme.{u}} {R S V : CommRingCat.{u}}
  (φ : R ⟶ S) (ψ : S ⟶ V)
  (g : Y ⟶ Spec R) (g' : Z ⟶ Spec S) (g'' : T ⟶ Spec V)
  (h : Z ⟶ Y) (j : T ⟶ Z)
  (w : h ≫ g = g' ≫ Spec.map φ)
  (w' : j ≫ g' = g'' ≫ Spec.map ψ)

/-- Compose actual coefficient maps into successive pushforwards, retaining
the canonical pushforward composition map. -/
def compositePushforwardModuleMap
    {M : Y.Modules} {N : Z.Modules} {P : T.Modules}
    (a : M ⟶ (Scheme.Modules.pushforward h).obj N)
    (b : N ⟶ (Scheme.Modules.pushforward j).obj P) :
    M ⟶ (Scheme.Modules.pushforward (j ≫ h)).obj P :=
  a ≫ (Scheme.Modules.pushforward h).map b ≫
    (Scheme.Modules.pushforwardComp j h).hom.app P

private lemma pushforwardCompositeAugmentation
    {P : T.Modules} {K : CochainComplex T.Modules ℕ}
    (ε : (CochainComplex.single₀ T.Modules).obj P ⟶ K) :
    mapResolutionAugmentation (Scheme.Modules.pushforward h)
        (mapResolutionAugmentation (Scheme.Modules.pushforward j) ε) ≫
        (Functor.mapHomologicalComplexCompIso
          (Scheme.Modules.pushforwardComp j h) _).hom.app K =
      (CochainComplex.single₀ Y.Modules).map
          ((Scheme.Modules.pushforwardComp j h).hom.app P) ≫
        mapResolutionAugmentation (Scheme.Modules.pushforward (j ≫ h)) ε := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, mapResolutionAugmentation_f_zero,
    Functor.mapHomologicalComplexCompIso_hom_app_f, CochainComplex.single₀_map_f_zero]
  exact (Scheme.Modules.pushforwardComp j h).hom.naturality (ε.f 0)

variable [IsClosedImmersion h] [IsClosedImmersion j]

/-- Precomposing an actual coefficient map precomposes its cohomology map. -/
@[reassoc]
lemma closedImmersionCohomologyMap_precomp
    {M M' : Y.Modules} {N : Z.Modules}
    (a : M ⟶ (Scheme.Modules.pushforward h).obj N) (b : M' ⟶ M) (n : ℕ) :
    closedImmersionCohomologyMap φ g g' h w (b ≫ a) n =
      (relativeCohomology g n).map b ≫
        closedImmersionCohomologyMap φ g g' h w a n := by
  simp only [closedImmersionCohomologyMap, Functor.map_comp, Category.assoc]

/-- Transitivity on the canonical composite-pushforward coefficient. -/
@[reassoc]
lemma closedImmersionCohomologyMap_pushforwardComp (P : T.Modules) (n : ℕ) :
    closedImmersionCohomologyMap (φ ≫ ψ) g g'' (j ≫ h)
        (sectionsBaseChangeSquare_comp φ ψ g g' g'' h j w w')
        ((Scheme.Modules.pushforwardComp j h).hom.app P) n ≫
        (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom.app
          ((relativeCohomology g'' n).obj P) =
      closedImmersionCohomologyMap φ g g' h w
          (𝟙 ((Scheme.Modules.pushforward h).obj
            ((Scheme.Modules.pushforward j).obj P))) n ≫
        (ModuleCat.restrictScalars φ.hom).map
          (closedImmersionCohomologyMap ψ g' g'' j w'
            (𝟙 ((Scheme.Modules.pushforward j).obj P)) n) := by
  have := ClosedImmersionHigherDirectImageVanishing.pushforward_preservesEpimorphisms h
  have := ClosedImmersionHigherDirectImageVanishing.pushforward_preservesEpimorphisms j
  have : (Scheme.Modules.pushforward h).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  have : (Scheme.Modules.pushforward j).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  let I := injectiveResolution P
  let η := mapResolutionAugmentation (Scheme.Modules.pushforward j) I.ι
  let ε := mapResolutionAugmentation (Scheme.Modules.pushforward h) η
  have hacyc (i q : ℕ) :
      IsZero (((relativeGlobalSections g).rightDerived (q + 1)).obj
        ((Scheme.Modules.pushforward h).obj
          ((Scheme.Modules.pushforward j).obj (I.cocomplex.X i)))) := by
    exact ((pushforwardInjectiveAcyclic T Y (j ≫ h) (I.cocomplex.X i)
      (I.injective i) q).2 R g).of_iso
        ((relativeCohomology g (q + 1)).mapIso
          ((Scheme.Modules.pushforwardComp j h).app (I.cocomplex.X i)))
  have : IsIso (resolutionComparison (relativeGlobalSections g) ε n) :=
    (acyclicResolutionComparisonStatement _ _ (relativeGlobalSections g) _ _ ε
      inferInstance hacyc _ _ (comp_lift_id ε _)).2 n
  have hφ := resolutionComparison_closedImmersionCohomologyMap φ g g' h w ε η
    (𝟙 _) (𝟙 _) (by
      simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      rfl) n
  have hψ := resolutionComparison_closedImmersionCohomologyMap ψ g' g'' j w' η I.ι
    (𝟙 _) (𝟙 _) (by
      simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      rfl) n
  have hc := resolutionComparison_closedImmersionCohomologyMap (φ ≫ ψ) g g'' (j ≫ h)
    (sectionsBaseChangeSquare_comp φ ψ g g' g'' h j w w') ε I.ι
    ((Scheme.Modules.pushforwardComp j h).hom.app P)
    ((Functor.mapHomologicalComplexCompIso
      (Scheme.Modules.pushforwardComp j h) _).hom.app I.cocomplex)
    (pushforwardCompositeAugmentation h j I.ι) n
  have hn := (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom.naturality
    (resolutionComparison (relativeGlobalSections g'') I.ι n)
  have hd := resolutionCohomologyBaseChangeMap_comp φ ψ g g' g'' h j w w'
    (𝟙 (((Scheme.Modules.pushforward h).mapHomologicalComplex _).obj
      (((Scheme.Modules.pushforward j).mapHomologicalComplex _).obj I.cocomplex)))
    (𝟙 (((Scheme.Modules.pushforward j).mapHomologicalComplex _).obj I.cocomplex)) n
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hd
  change resolutionComparison (relativeGlobalSections g) ε n ≫
      closedImmersionCohomologyMap φ g g' h w (𝟙 _) n =
    resolutionCohomologyBaseChangeMap φ g g' h w (𝟙 _) n ≫
      (ModuleCat.restrictScalars φ.hom).map
        (resolutionComparison (relativeGlobalSections g') η n) at hφ
  change resolutionComparison (relativeGlobalSections g') η n ≫
      closedImmersionCohomologyMap ψ g' g'' j w' (𝟙 _) n =
    resolutionCohomologyBaseChangeMap ψ g' g'' j w' (𝟙 _) n ≫
      (ModuleCat.restrictScalars ψ.hom).map
        (resolutionComparison (relativeGlobalSections g'') I.ι n) at hψ
  change resolutionComparison (relativeGlobalSections g) ε n ≫
      closedImmersionCohomologyMap (φ ≫ ψ) g g'' (j ≫ h)
        (sectionsBaseChangeSquare_comp φ ψ g g' g'' h j w w')
        ((Scheme.Modules.pushforwardComp j h).hom.app P) n =
    resolutionCohomologyBaseChangeMap (φ ≫ ψ) g g'' (j ≫ h)
      (sectionsBaseChangeSquare_comp φ ψ g g' g'' h j w w')
      ((Functor.mapHomologicalComplexCompIso
        (Scheme.Modules.pushforwardComp j h) _).hom.app I.cocomplex) n ≫
      (ModuleCat.restrictScalars (φ ≫ ψ).hom).map
        (resolutionComparison (relativeGlobalSections g'') I.ι n) at hc
  simp only [Functor.comp_map] at hn
  apply (cancel_epi (resolutionComparison (relativeGlobalSections g) ε n)).1
  rw [← Category.assoc, hc, Category.assoc]
  erw [hn]
  rw [← Category.assoc]
  erw [hd]
  simp only [Category.assoc]
  erw [← Functor.map_comp, ← hψ, Functor.map_comp, ← Category.assoc, ← hφ]
  simp only [Category.assoc]

/-- Actual coefficient maps into successive closed-immersion pushforwards
induce the composite canonical cohomology map. -/
@[reassoc]
lemma closedImmersionCohomologyMap_comp
    {M : Y.Modules} {N : Z.Modules} {P : T.Modules}
    (a : M ⟶ (Scheme.Modules.pushforward h).obj N)
    (b : N ⟶ (Scheme.Modules.pushforward j).obj P) (n : ℕ) :
    closedImmersionCohomologyMap (φ ≫ ψ) g g'' (j ≫ h)
        (sectionsBaseChangeSquare_comp φ ψ g g' g'' h j w w')
        (compositePushforwardModuleMap h j a b) n ≫
        (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom.app
          ((relativeCohomology g'' n).obj P) =
      closedImmersionCohomologyMap φ g g' h w a n ≫
        (ModuleCat.restrictScalars φ.hom).map
          (closedImmersionCohomologyMap ψ g' g'' j w' b n) := by
  have hn := closedImmersionCohomologyMap_naturality φ g g' h w a
    (𝟙 ((Scheme.Modules.pushforward h).obj ((Scheme.Modules.pushforward j).obj P)))
    (a ≫ (Scheme.Modules.pushforward h).map b) b (by simp) n
  rw [compositePushforwardModuleMap, ← Category.assoc, closedImmersionCohomologyMap_precomp,
    Category.assoc, closedImmersionCohomologyMap_pushforwardComp φ ψ g g' g'' h j w w',
    ← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  congr 2
  exact (closedImmersionCohomologyMap_precomp ψ g' g'' j w' (𝟙 _) b n).symm.trans
    (by simp only [Category.comp_id])

end Langlands.AlgebraicGeometry.Modules.DerivedSections
