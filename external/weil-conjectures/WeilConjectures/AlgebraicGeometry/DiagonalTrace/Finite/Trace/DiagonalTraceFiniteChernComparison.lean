/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1KummerChernRealization
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation

/-! # Finite realization of the positive Chern component

Source: blueprint latest, diagonal-tower trace proof (1), identification of the
level map with the unit and section-class map of (G2). This comparison of arrows
uses Kummer normalization, not invertibility or cohomology of (G2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard
  Padic Padic.coefficientExtensionIntegers
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

private theorem evaluation_adjunct
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (ad : L ⊣ R) (ad' : L' ⊣ R') (F : C ⥤ C') (G : D ⥤ D')
    (p : L ⋙ G ≅ F ⋙ L') (q : R ⋙ F ≅ G ⋙ R')
    (hu : ∀ M, F.map (ad.unit.app M) ≫ q.hom.app (L.obj M) ≫
      R'.map (p.hom.app M) = ad'.unit.app (F.obj M))
    {M : C} {N : D} (f : L.obj M ⟶ N) :
    F.map ((ad.homEquiv M N) f) ≫ q.hom.app N =
      (ad'.homEquiv _ _) (p.inv.app M ≫ G.map f) := by
  have hunit : F.map (ad.unit.app M) ≫ q.hom.app (L.obj M) =
      ad'.unit.app (F.obj M) ≫ R'.map (p.inv.app M) := by
    apply (Iso.eq_comp_inv (R'.mapIso (p.app M))).2
    simpa only [Functor.mapIso_hom, Iso.app_hom, Category.assoc] using hu M
  rw [Adjunction.homEquiv_unit, F.map_comp, Category.assoc]
  rw [show F.map (R.map f) ≫ q.hom.app N =
    q.hom.app (L.obj M) ≫ R'.map (G.map f) from q.hom.naturality f]
  rw [← Category.assoc, hunit]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

private theorem realization_adjunct
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (ad : L ⊣ R) (ad' : L' ⊣ R') (F : C' ⥤ C) (G : D' ⥤ D)
    (p : F ⋙ L ≅ L' ⋙ G) (q : G ⋙ R ≅ R' ⋙ F)
    (hu : ∀ M, ad.unit.app (F.obj M) ≫ R.map (p.hom.app M) ≫
      q.hom.app (L'.obj M) = F.map (ad'.unit.app M))
    {M : C} {M' : C'} {N' : D'} (a : M ≅ F.obj M')
    (f : L'.obj M' ⟶ N') :
    (ad.homEquiv _ _) (L.map a.hom ≫ p.hom.app M' ≫ G.map f) ≫ q.hom.app N' =
      a.hom ≫ F.map ((ad'.homEquiv _ _) f) := by
  have hq : R.map (G.map f) ≫ q.hom.app N' =
      q.hom.app (L'.obj M') ≫ F.map (R'.map f) := q.hom.naturality f
  have ha : a.hom ≫ ad.unit.app (F.obj M') =
      ad.unit.app M ≫ R.map (L.map a.hom) := ad.unit.naturality a.hom
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% ha, hq]
  simpa only [Category.assoc] using
    congrArg (fun k => a.hom ≫ k ≫ F.map (R'.map f)) (hu M')

/-- Realization of the positive Chern adjunct, before any untwisting.

Source: `sk-prop-diagonal-tower-trace.proof.md` (1), identification of the
level map with (G2); `lemma-cohomology-projective-line-trace`, the Chern component of the
positively twisted decomposition.
(blueprint: lem-sfb-diagonal-trace-finite-chern-comparison).

Proof: finiteP1_coefficient_adjunction_coordinates supplies normalized
coefficient coordinates and the finite pull/push comparisons p,q, together
with their unit equation and coefficient-pullback equation. The scalar theorem
finiteP1_kummer_chern_realization identifies the evaluated Chern arrow on X
before direct image, giving the positive-line isomorphism t.

The generic helper evaluation_adjunct derives evaluation of any adjunct from
the unit equation of geometry_adjunction_evaluation and naturality of the
push comparison. Apply it to cp.derivedIso followed by the Chern arrow.
Compose pushEvaluation with the finite direct image of t and the component
of q to construct v. The coefficient and scalar-Chern squares identify the
resulting finite unadjointed arrow. The generic helper realization_adjunct
uses the finite unit equation and naturality to transport its adjunct.
Finally finiteP1PositiveClass_adjunct identifies the ordinary adjunct with
the second component of geoP1TwistedMap by its actual Kummer definition.
This uses no inverse decomposition, negative twist or cohomology vanishing.
All formulas also apply at n=0, on empty schemes and over the zero ring. -/
theorem diagonalTrace_finite_chern_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (b : SpTowerShriek.Base l E) {f : X ⟶ S}
    (e : X ≅ ProjectiveLine S) (he : e.hom ≫ (ProjectiveLine S ↘ S) = f)
    (g : SpTowerShriek.Geometry l E b f)
    (cp : CoefficientPullback l E b f g)
    (cX : Chern l E X) (hc : FiniteChernNormalization l E cX)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ) [Finite (SpTowerShriek.R l E n)] :
    let A := FiniteRing l E n
    let hA : ((l ^ (n + 1) : ℕ) : A) = 0 :=
      ULift.ext (coefficient_annihilates l E n)
    let hNS : IsUnit ((l ^ (n + 1) : ℕ) : Γ(S, ⊤)) := by
      simpa only [Nat.cast_pow] using hS.pow (n + 1)
    let F := (Scheme.sfIntrinsicModuleEquivalence S (SpTowerShriek.R l E n)).functor
    let adjunct := (SpTowerShriek.adjunction l E b g).homEquiv _ _
      ((cp.derivedIso l E).hom ≫
        firstChern l E cX (Scheme.Pic.mapHom e.hom (hyperplanePic S)))
    ∃ (a : (SpTowerShriek.Ev l E S n).obj (unit S (Arings l E S)) ≅
        F.mapDerivedCategory.obj (geoP1Unit A S))
      (v : (SpTowerShriek.Ev l E S n).obj
          ((SpTowerShriek.push l E b g).obj ((line l E cX)⟦(2 : ℤ)⟧)) ≅
        F.mapDerivedCategory.obj
          ((geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
            (geoP1Twist A (l ^ (n + 1)) hA (ProjectiveLine S) 1 2))),
      (SpTowerShriek.Ev l E S n).map adjunct ≫ v.hom =
        a.hom ≫ F.mapDerivedCategory.map
          (biprod.inr ≫ geoP1TwistedMap A (l ^ (n + 1))
            (pow_pos (Fact.out : l.Prime).pos _) hA S hNS) := by
  dsimp only
  obtain ⟨hX, cX', cS, p, q, hu, hcp⟩ :=
    finiteP1_coefficient_adjunction_coordinates l E b e he g cp hS n
  obtain ⟨t, ht⟩ := finiteP1_kummer_chern_realization l E e cX hc hS n cX'
  let F := (Scheme.sfIntrinsicModuleEquivalence S
    (SpTowerShriek.R l E n)).functor.mapDerivedCategory
  let H := finiteOverRealization l E n e
  let R := (Scheme.proEtaleConstantRingPushforward
    (SpTowerShriek.R l E n) f).rightDerivedFunctor
  let ad := (Scheme.proEtaleConstantRingAdjunction
    (SpTowerShriek.R l E n) f).mapDerivedCategoryRightDerivedAdjunction
  let a := finiteUnitCoordinate l E n S cS
  let N : DerivedCategory (Systems X (Arings l E X)) := (line l E cX)⟦(2 : ℤ)⟧
  let v := (g.pushEvaluation n).app N ≪≫
    R.mapIso t ≪≫ q.app _
  refine ⟨a, v, ?_⟩
  have heval := evaluation_adjunct (SpTowerShriek.adjunction l E b g) ad
    (SpTowerShriek.Ev l E S n) (SpTowerShriek.Ev l E X n)
    (g.pullEvaluation n) (g.pushEvaluation n)
    (SpTowerShriek.geometry_adjunction_evaluation l E b g n).1
    ((cp.derivedIso l E).hom ≫
      firstChern l E cX (Scheme.Pic.mapHom e.hom (hyperplanePic S)))
  have hclass :
      (g.pullEvaluation n).inv.app (unit S (Arings l E S)) ≫
        (SpTowerShriek.Ev l E X n).map
          ((cp.derivedIso l E).hom ≫
            firstChern l E cX (Scheme.Pic.mapHom e.hom (hyperplanePic S))) ≫ t.hom =
      (Scheme.proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) f).map a.hom ≫
        p.hom.app (geoP1Unit (FiniteRing l E n) S) ≫
        H.map ((geoP1UnitPullback (FiniteRing l E n) (ProjectiveLine S ↘ S)).hom ≫
          finiteP1PositiveClass l E S hS n) := by
    simp only [Functor.map_comp, Category.assoc]
    rw [ht]
    simpa only [Category.assoc] using
      congrArg (fun k => k ≫ H.map (finiteP1PositiveClass l E S hS n)) hcp
  let w := (g.pullEvaluation n).inv.app (unit S (Arings l E S)) ≫
    (SpTowerShriek.Ev l E X n).map
      ((cp.derivedIso l E).hom ≫
        firstChern l E cX (Scheme.Pic.mapHom e.hom (hyperplanePic S)))
  have hw : w ≫ t.hom =
      (Scheme.proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) f).map a.hom ≫
        p.hom.app (geoP1Unit (FiniteRing l E n) S) ≫
        H.map ((geoP1UnitPullback (FiniteRing l E n) (ProjectiveLine S ↘ S)).hom ≫
          finiteP1PositiveClass l E S hS n) := by
    simpa only [w, Category.assoc] using hclass
  have h₁ := congrArg (fun k => (k ≫ R.map t.hom) ≫ q.hom.app _) heval
  have h₂ := congrArg (fun k => k ≫ q.hom.app _)
    (ad.homEquiv_naturality_right w t.hom).symm
  have h₃ := congrArg (fun k => k ≫ q.hom.app _)
    (congrArg (ad.homEquiv _ _) hw)
  have h₄ := realization_adjunct ad
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (FiniteRing l E n))
      (ProjectiveLine S ↘ S)) F H p q hu a
    ((geoP1UnitPullback (FiniteRing l E n) (ProjectiveLine S ↘ S)).hom ≫
      finiteP1PositiveClass l E S hS n)
  have h₅ := congrArg (fun k => a.hom ≫ F.map k)
    (finiteP1PositiveClass_adjunct l E S hS n)
  simpa only [v, N, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
    h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

end AlgebraicGeometry.ProEtale.DiagonalTrace
