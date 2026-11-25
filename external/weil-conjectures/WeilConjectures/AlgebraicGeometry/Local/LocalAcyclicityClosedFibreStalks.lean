/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityAbelianSheaf
import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityStrictFibreComparison
import WeilConjectures.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedFiberComparison
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Stalk cohomology of the geometric-fibre pushforward

## References

* Stacks Project, Tag 0GJU, displayed stalk calculation
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem nonempty_cohomology_iso_of_iso_over
    {X Y Z : Scheme.{u}} (e : Y ≅ Z) (mY : Y ⟶ X) (mZ : Z ⟶ X)
    (he : e.hom ≫ mZ = mY)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ) :
    Nonempty
      ((cohomology AddCommGrpCat.{u + 1} Y q).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1} mY).obj G)) ≅
        (cohomology AddCommGrpCat.{u + 1} Z q).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1} mZ).obj G))) := by
  let H := (upperStar AddCommGrpCat.{u + 1} mZ).obj G
  let c : (upperStar AddCommGrpCat.{u + 1} mY).obj G ≅
      (upperStar AddCommGrpCat.{u + 1} e.hom).obj H :=
    (upperStarComp AddCommGrpCat.{u + 1} e.hom mZ mY he.symm).app G
  let d := (DerivedCategory.singleFunctor _ 0).mapIso c ≪≫
    ((upperStar AddCommGrpCat.{u + 1} e.hom).mapDerivedCategorySingleFunctor 0).symm.app H
  exact ⟨(cohomology AddCommGrpCat.{u + 1} Y q).mapIso d ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((upperStarCompRightDerivedGlobalSectionsIso AddCommGrpCat.{u + 1} e).app
        ((DerivedCategory.singleFunctor _ 0).obj H))⟩

/-- For an arbitrary coefficient sheaf, the nonnegative target stalks of the derived
unit on the closed fibre are the cohomology of a variety of vanishing cycles. No local
acyclicity is assumed. -/
theorem closedFibre_derivedUnit_target_stalks
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)
    {Ξ : Type u} [Field Ξ] [IsAlgClosed Ξ]
    (z : Spec (.of Ξ) ⟶
      pullback (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
        (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s)))) :
    let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
    let f' := pullback.snd f (Scheme.strictHenselizationStructuralMap s)
    let i := pullback.fst f' (Spec.map (CommRingCat.ofHom
      (Scheme.strictHenselizationRingPointEvaluation s)))
    let h := pullback.fst f' t
    let x := (z ≫ i) ≫ p
    ∃ e : Scheme.strictHenselizationScheme s ≅ Scheme.strictHenselizationScheme (x ≫ f),
      ∀ q : ℕ, Nonempty
        ((Scheme.pointSmallEtale z).sheafFiber.obj
            ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
              ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.obj
                (((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus ⋙
                  (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus).obj
                  ((DerivedCategory.Plus.singleFunctor _ 0).obj
                    ((upperStar AddCommGrpCat.{u + 1} p).obj G))))) ≅
          (cohomology AddCommGrpCat.{u + 1}
            (localAcyclicityFiber f x (t ≫ e.hom)) (q : ℤ)).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              ((upperStar AddCommGrpCat.{u + 1}
                (pullback.fst (localAcyclicityStrictMap f x) (t ≫ e.hom) ≫
                  Scheme.strictHenselizationStructuralMap x)).obj G))) := by
  dsimp only
  let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
  let f' := pullback.snd f (Scheme.strictHenselizationStructuralMap s)
  let i := pullback.fst f' (Spec.map (CommRingCat.ofHom
    (Scheme.strictHenselizationRingPointEvaluation s)))
  let h := pullback.fst f' t
  let x' := z ≫ i
  let x := x' ≫ p
  have : IsAffine (Scheme.strictHenselizationScheme s) := by
    change IsAffine (Spec (Scheme.strictHenselizationRing s))
    infer_instance
  have ht : IsAffineHom t := inferInstance
  have hh : IsAffineHom h := MorphismProperty.pullback_fst f' t ht
  have hclosed : x' ≫ f' = (z ≫ pullback.snd f'
      (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s)))) ≫
        Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s)) := by
    simpa only [x', i, Category.assoc] using congrArg (fun a ↦ z ≫ a)
      (pullback.condition (f := f') (g := Spec.map (CommRingCat.ofHom
        (Scheme.strictHenselizationRingPointEvaluation s))))
  obtain ⟨_, e, E, _, hE⟩ := localAcyclicity_strict_fibre_comparison f s p f'
    (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)) x'
    (z ≫ pullback.snd f' (Spec.map (CommRingCat.ofHom
      (Scheme.strictHenselizationRingPointEvaluation s)))) hclosed t
  refine ⟨e, fun q ↦ ?_⟩
  let G' := (upperStar AddCommGrpCat.{u + 1} p).obj G
  let F := (upperStar AddCommGrpCat.{u + 1} h).obj G'
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G'
  let L := (upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus.obj K
  let R := (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus
  let H := DerivedCategory.Plus.homologyFunctor
    (Sheaf (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (q : ℤ)
  let Φ := (Scheme.pointSmallEtale z).sheafFiber (A := AddCommGrpCat.{u + 1})
  let Ψ := (Scheme.pointSmallEtale x').sheafFiber (A := AddCommGrpCat.{u + 1})
  let d : L ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj F :=
    ((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlusSingleFunctor 0).app G'
  let cStalk := upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} i z
  let c := Φ.mapIso
      (((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlusHomologyFunctorIso
        (q : ℤ)).symm.app (R.obj L)) ≪≫
    cStalk.app (H.obj (R.obj L)) ≪≫
    Ψ.mapIso (H.mapIso (R.mapIso d))
  obtain ⟨r, _, hr⟩ := unrestricted_strictHenselization_stalk h x' F q
  let ρ := Scheme.strictHenselizationStructuralMap x'
  let W := pullback h ρ
  let w := pullback.fst h ρ
  let mW := (w ≫ h) ≫ p
  let mV := pullback.fst (localAcyclicityStrictMap f x) (t ≫ e.hom) ≫
    Scheme.strictHenselizationStructuralMap x
  let cF : (upperStar AddCommGrpCat.{u + 1} w).obj F ≅
      (upperStar AddCommGrpCat.{u + 1} mW).obj G :=
    ((upperStarComp AddCommGrpCat.{u + 1} w h).symm.app G') ≪≫
      ((upperStarComp AddCommGrpCat.{u + 1} (w ≫ h) p).symm.app G)
  let E0 : W ≅ pullback (ρ ≫ f') t :=
    pullbackSymmetry h ρ ≪≫ pullbackRightPullbackFstIso f' t ρ
  let E' := E0 ≪≫ E
  have hE' : E'.hom ≫ mV = mW := by
    simp only [E', Iso.trans_hom, mV, Category.assoc]
    rw [hE]
    change E0.hom ≫ pullback.fst (ρ ≫ f') t ≫ ρ ≫ p = mW
    simp only [E0, Iso.trans_hom, Category.assoc,
      pullbackRightPullbackFstIso_hom_fst_assoc]
    change (pullbackSymmetry h ρ).hom ≫ pullback.fst ρ h ≫ ρ ≫ p = mW
    calc
      _ = pullback.snd h ρ ≫ ρ ≫ p := by
        simpa only [Category.assoc] using congrArg (fun a ↦ a ≫ ρ ≫ p)
          (pullbackSymmetry_hom_comp_fst h ρ)
      _ = mW := by
        simpa only [mW, w, Category.assoc] using
          (congrArg (fun a ↦ a ≫ p) (pullback.condition (f := h) (g := ρ))).symm
  obtain ⟨cV⟩ := nonempty_cohomology_iso_of_iso_over E' mW mV hE' G (q : ℤ)
  let σ := Scheme.strictLocalizationToBase x'
  let ι : Scheme.strictHenselizationScheme x' ⟶ Scheme.strictLocalization x' :=
    Spec.map (Scheme.smallStrictHenselizationColimitIso x').inv
  have hι : ι ≫ σ = ρ := Scheme.smallStrictHenselizationColimitIso_toBase x'
  let g : W ⟶ pullback h σ :=
    pullback.map h ρ h σ (𝟙 _) ι (𝟙 _) (by simp) (by simpa using hι.symm)
  have : IsIso g := by dsimp only [g]; infer_instance
  obtain ⟨cWN⟩ := nonempty_cohomology_iso_of_iso_over (asIso g) w
    (pullback.fst h σ) (by
      change g ≫ pullback.fst h σ = w
      dsimp only [g]
      rw [pullback.lift_fst, Category.comp_id]) F (q : ℤ)
  exact ⟨c ≪≫ asIso (r ≫ strictHenselizationCohomologyComparison x' h F q) ≪≫
    (cohomology AddCommGrpCat.{u + 1} (pullback h σ) (q : ℤ)).mapIso
      ((DerivedCategory.Plus.singleFunctorιIso _ 0).app
        ((upperStar AddCommGrpCat.{u + 1} (pullback.fst h σ)).obj F)) ≪≫ cWN.symm ≪≫
    (cohomology AddCommGrpCat.{u + 1} W (q : ℤ)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso cF) ≪≫ cV⟩

end AlgebraicGeometry.Etale
