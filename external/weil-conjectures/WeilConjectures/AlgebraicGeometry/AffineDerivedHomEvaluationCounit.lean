/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.FiniteSheafHomAffineAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomUnitIso
import WeilConjectures.AlgebraicGeometry.AffineDerivedHomLocalizedEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # AffineDerivedHomEvaluationCounit

Source: Stacks Project, Duality for Schemes, Section 48.11.
-/

@[expose] public section

universe u wY wA

open CategoryTheory Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

private theorem transportEvaluation
    {C A : Type*} [Category C] [Category A]
    {L ρ : A ⥤ C} {R : C ⥤ A} {F G : C ⥤ C}
    (adj : L ⊣ R) (e : L ≅ ρ) (p : F ⟶ G) (ι : G ≅ 𝟭 C)
    {K₀ K : C} (q : K₀ ≅ K) (d₀ : L.obj (R.obj K₀) ≅ F.obj K₀)
    (hd₀ : d₀.hom ≫ p.app K₀ ≫ ι.hom.app K₀ = adj.counit.app K₀) :
    ∃ d : ρ.obj (R.obj K) ≅ F.obj K,
      d.hom ≫ p.app K ≫ ι.hom.app K = (adj.ofNatIsoLeft e).counit.app K := by
  refine ⟨(e.app (R.obj K)).symm ≪≫ L.mapIso (R.mapIso q.symm) ≪≫ d₀ ≪≫
    F.mapIso q, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [p.naturality_assoc, ι.hom.naturality]
  change e.inv.app (R.obj K) ≫ (R ⋙ L).map q.inv ≫
    d₀.hom ≫ p.app K₀ ≫ ι.hom.app K₀ ≫ q.hom = _
  have hd := congrArg (fun z ↦ z ≫ q.hom) hd₀
  simp only [Category.assoc] at hd
  rw [hd]
  rw [adj.counit.naturality_assoc q.inv]
  simp [q.inv_hom_id]

private theorem transportEvaluationFromRepresentatives
    {C A D : Type*} [Category C] [Category A] [Category D]
    (Q : D ⥤ C) [Q.EssSurj] {ρ : A ⥤ C} {F G : C ⥤ C}
    (p : F ⟶ G) (ι : G ≅ 𝟭 C)
    (h : ∃ (R : C ⥤ A) (L : A ⥤ C) (_e : L ≅ ρ) (adj : L ⊣ R),
      ∀ (j : G ≅ 𝟭 C) (K : D), ∃ d : L.obj (R.obj (Q.obj K)) ≅ F.obj (Q.obj K),
        d.hom ≫ p.app (Q.obj K) ≫ j.hom.app (Q.obj K) = adj.counit.app (Q.obj K)) :
    ∃ (R : C ⥤ A) (adj : ρ ⊣ R) (j : G ≅ 𝟭 C), ∀ K : C,
      ∃ d : ρ.obj (R.obj K) ≅ F.obj K,
        d.hom ≫ p.app K ≫ j.hom.app K = adj.counit.app K := by
  obtain ⟨R, L, e, adj, h⟩ := h
  refine ⟨R, adj.ofNatIsoLeft e, ι, ?_⟩
  intro K
  obtain ⟨d, hd⟩ := h ι (Q.objPreimage K)
  exact transportEvaluation adj e p ι (Q.objObjPreimageIso K) d hd

private noncomputable def affineScalarLocalizationIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))]
    (L : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    (t : DerivedCategory.Q ⋙ L ≅
      (SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f))
        ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).mapHomologicalComplex
          (.up ℤ) ⋙ DerivedCategory.Q) :
    L ≅ (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f))
      ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor := by
  let B : Y.CommAlgebraSheaf := Under.mk (⟨f.c⟩ : Y.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf)
  let T := SheafOfModules.restrictScalars
    (R := moduleRings Y.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace f))
    ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩
  haveI : HasDerivedCategory.{wA} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right)) := by
    dsimp [B]
    exact inferInstanceAs (HasDerivedCategory.{wA}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))))
  haveI : CategoryTheory.Limits.PreservesFiniteLimits T :=
    sheafAlgebraRestrictScalars_preservesFiniteLimits Y B
  haveI : CategoryTheory.Limits.PreservesFiniteColimits T :=
    sheafAlgebraRestrictScalars_preservesFiniteColimits Y B
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) _).preimageIso
      (t ≪≫ T.mapDerivedCategoryFactors.symm) ≪≫
        T.rightDerivedFunctorIsoMapDerivedCategory.symm


private theorem exists_affine_localizedEvaluation {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))] :
    let C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let A := SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))
    let S := SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f))
      ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩
    let B := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let U := (DerivedCategory.singleFunctor C 0).obj (SheafOfModules.unit Y.ringCatSheaf)
    let M := (DerivedCategory.singleFunctor C 0).obj
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
    let p := (Functor.curry.obj B).map
      (((DerivedCategory.singleFunctor C 0).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).op)
    ∃ (R : DerivedCategory C ⥤ DerivedCategory A)
      (L : DerivedCategory A ⥤ DerivedCategory C)
      (_e : L ≅ S.rightDerivedFunctor) (adj : L ⊣ R),
      ∀ (ι : (Functor.curry.obj B).obj (op U) ≅ 𝟭 _) (K : CochainComplex C ℤ),
      ∃ d : L.obj (R.obj (DerivedCategory.Q.obj K)) ≅ B.obj (op M, DerivedCategory.Q.obj K),
        d.hom ≫ p.app (DerivedCategory.Q.obj K) ≫ ι.hom.app (DerivedCategory.Q.obj K) =
          adj.counit.app (DerivedCategory.Q.obj K) := by
  refine (exists_affine_derivedSheafHom_adjunction.{u, wY, wA} f).elim fun H₀ h₀ ↦ ?_
  refine h₀.elim fun hH₀ h₁ ↦ ?_
  let _ := hH₀
  refine h₁.elim fun iH h₂ ↦ ?_
  refine h₂.elim fun adj₀ h₃ ↦ ?_
  refine h₃.2.elim fun R h₄ ↦ ?_
  refine h₄.elim fun β h₅ ↦ ?_
  refine h₅.elim fun L h₆ ↦ ?_
  refine h₆.elim fun t h₇ ↦ ?_
  refine h₇.elim fun adj h₈ ↦ ?_
  exact ⟨R, L, affineScalarLocalizationIso.{u, wY, wA} f L t, adj, fun ι K ↦
    affine_derivedHom_localized_evaluation.{u, wY, wA}
      f H₀ iH adj₀ h₃.1 R β L t adj h₈.1 h₈.2.2.2 ι K⟩

/-- The affine algebra-valued derived Hom adjunction, with its evaluation counit.
This lemma involves neither a quasi-coherent right adjoint of pushforward nor its
comparison with scalar restriction.

Source: Stacks Project, Tags 0BUZ, 0BV0 and 0AX3
(blueprint: lem-sc-affine-derived-hom-evaluation-counit).

Proof:
1. Take the underived sheaf-Hom adjunction and its derived adjunction from
   `exists_affine_derivedSheafHom_adjunction`. Scalar restriction is exact, so its
   derived functor L is canonically isomorphic to the chosen rightDerivedFunctor.
   Transport the adjunction across that isomorphism, obtaining H and adjH.
2. Compute on a K-injective resolution I of K. After forgetting the algebra action,
   H(K) is Hom(A,I); identify A with the module f_* O_X by the identity on sections.
   The localization comparison for derivedInternalHom gives the displayed d.
3. Hom(O_Y,I) is canonically I, by evaluation at one in every degree. Descend this
   natural chain isomorphism and the resolution quasi-isomorphism to obtain iota.
4. Precomposition by O_Y -> A followed by that evaluation sends a local map to its
   value at one. The derived counit formula of the affine adjunction is the same
   chain map. Localization and its natural comparison therefore give the equality.
The argument works for all derived objects, including zero and arbitrary shifts. -/
theorem exists_affine_derivedHom_evaluation_counit {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))] :
    ∃ (H : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))))
      (adjH : (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f))
      ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ⊣ H),
    ∃ ι : (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _,
    ∀ K : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
    ∃ d : (SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor.obj
          (H.obj K) ≅
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))),
            K),
    d.hom ≫ (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).map
        (((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).op, 𝟙 K) ≫
        ι.hom.app K = adjH.counit.app K := by
  exact transportEvaluationFromRepresentatives DerivedCategory.Q
    ((Functor.curry.obj
      (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).map
        (((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).op))
    (Classical.choice (derivedInternalHom_unit_iso.{u, wY} Y))
    (exists_affine_localizedEvaluation.{u, wY, wA} f)

end AlgebraicGeometry
