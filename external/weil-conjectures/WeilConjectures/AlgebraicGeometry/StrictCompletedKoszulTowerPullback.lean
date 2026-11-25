/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import WeilConjectures.AlgebraicGeometry.CompletedKoszulDualTowerPullback
import WeilConjectures.AlgebraicGeometry.RingedComplexTensorPullback

/-! # Finite augmented Koszul towers under inverse image

Source: Stacks Project, algebraization.tex, Tag 0A0E; sites-cohomology.tex, Tag 07A4.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.ConstantCompletion

/-- Inverse image identifies the actual finite Koszul tensor towers and their
coaugmentations, before taking any inverse limit or passing to derived categories.

Source: Stacks Project, algebraization.tex, Tag 0A0E, finite Koszul calculation;
sites-cohomology.tex, Tag 07A4, pullback of tensor products.
(auxiliary; not a blueprint node).

Proof: identify pullback along the invertible completed coefficient map with pure
module inverse image. In degree q the ordered dual Koszul tensor has its finite
biproduct decomposition indexed by subsets of the generators, with the summand
indexed by E equal to N.X (q + card E). The inverse image of each summand is the
corresponding target summand. The tensor comparison supplies this identification
canonically. The differential is the differential of N together with signed scalar
multiplications by a_i^(m+1). The constant-ring comparison, natural in all rings,
identifies the constant scalar a_i, and the completed coefficient comparison does
so after every finite projection. Thus it identifies these differentials and the
transition maps, which multiply by a_i on the selected factors and are identity on
the others. The comparisons are natural in chain maps N. Their inverse maps are
obtained from the inverse finite biproduct and rank-one comparisons. The
coaugmentation has identity on its empty-subset coordinate and zero elsewhere,
so its stated compatibility follows coordinatewise. For r=0 the sole coordinate
is N itself; zero scalars, repeated scalars and zero rings obey the same formulas.
-/
theorem strictCompletedKoszulTowerPullback
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)}
    (F : InverseImageData L) (V : Sheaf K (Type v) ⥤ Sheaf J (Type v))
    (adj : L ⊣ V) [PreservesFiniteLimits L]
    (A : Type v) [CommRing A] (I : Ideal A) [IsIso (completedMap F A I)]
    (r : ℕ) (a : Fin r → A) :
    let P := pull F (completedMap F A I)
    let TX := ringedKoszulTensorTowerFunctor (completed J A I) r
      (fun i ↦ algebraSection (baseMap J A I true) (a i))
    let TS := ringedKoszulTensorTowerFunctor (completed K A I) r
      (fun i ↦ algebraSection (baseMap K A I true) (a i))
    ∃ h : TX ⋙ ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapHomologicalComplex
          (.up ℤ) ≅ P.mapHomologicalComplex (.up ℤ) ⋙ TS,
      ∀ (N : Cx (completed J A I)) (m : ℕᵒᵖ) (n : ℤ),
        P.map ((ringedKoszulTensorUnitComponent (completed J A I) r
          (fun i ↦ algebraSection (baseMap J A I true) (a i)) N m).f n) ≫
            ((h.hom.app N).f n).app m =
          (ringedKoszulTensorUnitComponent (completed K A I) r
            (fun i ↦ algebraSection (baseMap K A I true) (a i))
            ((P.mapHomologicalComplex (.up ℤ)).obj N) m).f n := by
  let R := completed J A I
  let S := completed K A I
  let P : Mod R ⥤ Mod S := pull F (completedMap F A I)
  let Pc : Cx R ⥤ Cx S := P.mapHomologicalComplex (.up ℤ)
  let b : Fin r → (R.obj ⋙ forget CommRingCat).sections :=
    fun i ↦ algebraSection (baseMap J A I true) (a i)
  let d : Fin r → (S.obj ⋙ forget CommRingCat).sections :=
    fun i ↦ algebraSection (baseMap K A I true) (a i)
  let QX : ℕᵒᵖ ⥤ Cx R := ringedKoszulDualTower R r b
  let QS : ℕᵒᵖ ⥤ Cx S := ringedKoszulDualTower S r d
  obtain ⟨tc⟩ := ringedComplexTensorPullback F V adj
    (R := R) (S := S) (completedMap F A I)
  let j := tc.j
  let t := tc.t
  have htr := tc.rightNaturality
  have htl := tc.leftNaturality
  have ht := tc.unit
  have he' : ∃ e : QX ⋙ Pc ≅ QS,
      ∀ m : ℕ, Pc.map (ringedKoszulDualUnit R r b m) ≫ e.hom.app (op m) =
        j.hom ≫ ringedKoszulDualUnit S r d m :=
    completedKoszulDualTowerPullback F V adj A I r a j
  obtain ⟨e, he⟩ := he'
  let hN (N : Cx R) : (ringedKoszulTensorTower R r b).obj N ⋙ Pc ≅
      (ringedKoszulTensorTower S r d).obj (Pc.obj N) :=
    NatIso.ofComponents
      (fun m ↦ t N (QX.obj m) ≪≫
        ((ringedKoszulTensor S).obj (Pc.obj N)).mapIso (e.app m)) (by
      intro m k f
      have h₁ := htr N (QX.obj m) (QX.obj k) (QX.map f)
      change Pc.map (((ringedKoszulTensor R).obj N).map (QX.map f)) ≫
          (t N (QX.obj k)).hom =
        (t N (QX.obj m)).hom ≫
          ((ringedKoszulTensor S).obj (Pc.obj N)).map (Pc.map (QX.map f)) at h₁
      change Pc.map (((ringedKoszulTensor R).obj N).map (QX.map f)) ≫
          ((t N (QX.obj k)).hom ≫
            ((ringedKoszulTensor S).obj (Pc.obj N)).map (e.hom.app k)) =
        ((t N (QX.obj m)).hom ≫
          ((ringedKoszulTensor S).obj (Pc.obj N)).map (e.hom.app m)) ≫
          ((ringedKoszulTensor S).obj (Pc.obj N)).map (QS.map f)
      rw [← Category.assoc, h₁]
      simp only [Category.assoc, ← Functor.map_comp]
      congr 2
      exact e.hom.naturality f)
  let H (N : Cx R) :
      (((Functor.whiskeringRight ℕᵒᵖ (Mod R) (Mod S)).obj P).mapHomologicalComplex
        (.up ℤ)).obj ((ringedKoszulTensorTowerFunctor R r b).obj N) ≅
      (ringedKoszulTensorTowerFunctor S r d).obj (Pc.obj N) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ NatIso.ofComponents
        (fun m ↦ (HomologicalComplex.eval (Mod S) (.up ℤ) n).mapIso ((hN N).app m))
        (by
          intro m k f
          exact congrArg (fun g ↦ g.f n) ((hN N).hom.naturality f)))
      (by
        intro n k h
        apply NatTrans.ext
        funext m
        have hk : n + 1 = k := h
        subst k
        simp only [ringedKoszulTensorTowerFunctor, ringedKoszulTensorTowerComplex,
          Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d, NatTrans.comp_app,
          NatIso.ofComponents_hom_app, Functor.mapIso_hom, Functor.whiskerLeft_app,
          HomologicalComplex.dNatTrans_app]
        exact ((hN N).hom.app m).comm n (n + 1))
  refine ⟨NatIso.ofComponents H ?_, ?_⟩
  · intro N M f
    apply HomologicalComplex.hom_ext
    intro n
    apply NatTrans.ext
    funext m
    have h₁ := htl N M (QX.obj m) f
    change Pc.map (((ringedKoszulTensor R).map f).app (QX.obj m)) ≫
        (t M (QX.obj m)).hom =
      (t N (QX.obj m)).hom ≫
        ((ringedKoszulTensor S).map (Pc.map f)).app (Pc.obj (QX.obj m)) at h₁
    have h₂ := ((ringedKoszulTensor S).map (Pc.map f)).naturality (e.hom.app m)
    change ((ringedKoszulTensor S).obj (Pc.obj N)).map (e.hom.app m) ≫
        ((ringedKoszulTensor S).map (Pc.map f)).app (QS.obj m) =
      ((ringedKoszulTensor S).map (Pc.map f)).app (Pc.obj (QX.obj m)) ≫
        ((ringedKoszulTensor S).obj (Pc.obj M)).map (e.hom.app m) at h₂
    have h₃ :
        Pc.map (((ringedKoszulTensor R).map f).app (QX.obj m)) ≫
            (hN M).hom.app m =
          (hN N).hom.app m ≫
            ((ringedKoszulTensor S).map (Pc.map f)).app (QS.obj m) := by
      change Pc.map (((ringedKoszulTensor R).map f).app (QX.obj m)) ≫
          ((t M (QX.obj m)).hom ≫
            ((ringedKoszulTensor S).obj (Pc.obj M)).map (e.hom.app m)) =
        ((t N (QX.obj m)).hom ≫
          ((ringedKoszulTensor S).obj (Pc.obj N)).map (e.hom.app m)) ≫
          ((ringedKoszulTensor S).map (Pc.map f)).app (QS.obj m)
      rw [← Category.assoc, h₁, Category.assoc, ← h₂, ← Category.assoc]
    exact congrArg (fun z ↦ z.f n) h₃
  · intro N m n
    have hn := htr N (ringedSiteRingComplex R) (QX.obj m)
      (ringedKoszulDualUnit R r b m.unop)
    change Pc.map (((ringedKoszulTensor R).obj N).map
        (ringedKoszulDualUnit R r b m.unop)) ≫ (t N (QX.obj m)).hom =
      (t N (ringedSiteRingComplex R)).hom ≫
        ((ringedKoszulTensor S).obj (Pc.obj N)).map
          (Pc.map (ringedKoszulDualUnit R r b m.unop)) at hn
    have h : Pc.map (ringedKoszulTensorUnitComponent R r b N m) ≫
        (hN N).hom.app m =
        ringedKoszulTensorUnitComponent S r d (Pc.obj N) m := by
      change Pc.map ((ringedKoszulRightUnitIso R N).inv ≫
          ((ringedKoszulTensor R).obj N).map (ringedKoszulDualUnit R r b m.unop)) ≫
          ((t N (QX.obj m)).hom ≫
            ((ringedKoszulTensor S).obj (Pc.obj N)).map (e.hom.app m)) =
        (ringedKoszulRightUnitIso S (Pc.obj N)).inv ≫
          ((ringedKoszulTensor S).obj (Pc.obj N)).map (ringedKoszulDualUnit S r d m.unop)
      calc
        _ = Pc.map (ringedKoszulRightUnitIso R N).inv ≫
            (Pc.map (((ringedKoszulTensor R).obj N).map
              (ringedKoszulDualUnit R r b m.unop)) ≫
              (t N (QX.obj m)).hom) ≫
            ((ringedKoszulTensor S).obj (Pc.obj N)).map (e.hom.app m) := by
          simp only [Pc.map_comp, Category.assoc]
        _ = Pc.map (ringedKoszulRightUnitIso R N).inv ≫
            ((t N (ringedSiteRingComplex R)).hom ≫
              ((ringedKoszulTensor S).obj (Pc.obj N)).map
                (Pc.map (ringedKoszulDualUnit R r b m.unop))) ≫
            ((ringedKoszulTensor S).obj (Pc.obj N)).map (e.hom.app m) := by rw [hn]
        _ = (Pc.map (ringedKoszulRightUnitIso R N).inv ≫
            (t N (ringedSiteRingComplex R)).hom ≫
              ((ringedKoszulTensor S).obj (Pc.obj N)).map j.hom) ≫
            ((ringedKoszulTensor S).obj (Pc.obj N)).map
              (ringedKoszulDualUnit S r d m.unop) := by
          simp only [Category.assoc]
          rw [← Functor.map_comp, he, Functor.map_comp]
        _ = _ := by rw [ht]
    exact congrArg (fun z ↦ z.f n) h

end CategoryTheory.ConstantCompletion
