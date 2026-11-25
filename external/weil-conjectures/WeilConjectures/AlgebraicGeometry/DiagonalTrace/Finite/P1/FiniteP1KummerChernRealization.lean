/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1CoefficientAdjunctionCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1KummerBoundaryTransport

/-! # Scalar realization of the finite Kummer Chern class

Source: blueprint latest, diagonal-tower trace proof (1), identification of
the positive section class before taking its direct-image adjunct.
(blueprint: lem-sfb-finite-p1-kummer-chern-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard
  Padic Padic.coefficientExtensionIntegers AlgebraicGeometry.Etale.projectiveLineTraceDatum
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem comparison_adjunct
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (ad : L ⊣ R) (ad' : L' ⊣ R') (F : C ⥤ C') (G : D ⥤ D')
    (p : F ⋙ L' ≅ L ⋙ G) {M : C} {N : D} (f : L.obj M ⟶ N) :
    F.map ((ad.homEquiv _ _) f) ≫
        (ad'.homEquiv _ _) (p.hom.app (R.obj N) ≫ G.map (ad.counit.app N)) =
      (ad'.homEquiv _ _) (p.hom.app M ≫ G.map f) := by
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1
  have hn : L'.map (F.map ((ad.homEquiv _ _) f)) ≫ p.hom.app (R.obj N) =
      p.hom.app M ≫ G.map (L.map ((ad.homEquiv _ _) f)) :=
    p.hom.naturality ((ad.homEquiv _ _) f)
  rw [← Category.assoc, hn, Category.assoc, ← G.map_comp]
  have h : L.map ((ad.homEquiv _ _) f) ≫ ad.counit.app N = f :=
    (ad.homEquiv _ _).symm_apply_apply f
  rw [h]

/-- The comparison image of the normalized positive etale Kummer class.
Source: diagonal-tower trace (1), the section-class component of (G2)
(blueprint: lem-sfb-finite-p1-kummer-chern-realization). -/
def finiteP1PositiveClass (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ) [Finite (SpTowerShriek.R l E n)] :
    geoP1Unit (FiniteRing l E n) (ProjectiveLine S) ⟶
      geoP1Twist (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext (coefficient_annihilates l E n)) (ProjectiveLine S) 1 2 :=
  (geoP1Comparison (FiniteRing l E n) (ProjectiveLine S)).map
    (geoP1EtaleChern (FiniteRing l E n) (l ^ (n + 1))
      (pow_pos (Fact.out : l.Prime).pos _)
      (ULift.ext (coefficient_annihilates l E n)) S
      (by simpa only [Nat.cast_pow] using hS.pow (n + 1)))

attribute [local irreducible] finiteP1PositiveClass

private theorem ordinary_positive_adjunct
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (ProjectiveLine S ↘ S)).homEquiv _ _
        ((geoP1UnitPullback A (ProjectiveLine S ↘ S)).hom ≫
          (geoP1Comparison A (ProjectiveLine S)).map (geoP1EtaleChern A N hN hA S hS)) =
      biprod.inr ≫ geoP1TwistedMap A N hN hA S hS := by
  let d := Etale.projectiveLineTraceDatum N hN A hA S hS
  symm
  simp only [geoP1TwistedMap, geoP1SumComparison, biprod.inr_desc_assoc,
    ← Functor.map_comp_assoc]
  rw [d.decomposition_hom, biprod.inr_desc]
  unfold Etale.ordinaryFiniteP1ChernPushforward geoP1PushComparison
  have h := comparison_adjunct
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (ProjectiveLine S ↘ S))
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (ProjectiveLine S ↘ S))
    (geoP1Comparison A S) (geoP1Comparison A (ProjectiveLine S))
    (geoP1PullComparison A (ProjectiveLine S ↘ S))
    ((Etale.ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom ≫ d.chern)
  refine h.trans ?_
  congr 1
  simp only [geoP1UnitPullback, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rfl

/-- The second injection of the specified positive decomposition is the ordinary
adjunct of its Kummer class. This uses the defining component, not invertibility.
Source: diagonal-tower trace (1), definition of (G2)
(blueprint: lem-sfb-finite-p1-kummer-chern-realization). -/
theorem finiteP1PositiveClass_adjunct (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ) [Finite (SpTowerShriek.R l E n)] :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (FiniteRing l E n))
      (ProjectiveLine S ↘ S)).homEquiv _ _
        ((geoP1UnitPullback (FiniteRing l E n) (ProjectiveLine S ↘ S)).hom ≫
          finiteP1PositiveClass l E S hS n) =
      biprod.inr ≫ geoP1TwistedMap (FiniteRing l E n) (l ^ (n + 1))
        (pow_pos (Fact.out : l.Prime).pos _)
        (ULift.ext (coefficient_annihilates l E n)) S
        (by simpa only [Nat.cast_pow] using hS.pow (n + 1)) := by
  unfold finiteP1PositiveClass
  exact ordinary_positive_adjunct _ _ _ _ S _

/-- Finite Kummer normalization determines the coefficient-linear class itself,
with no tower pushforward or coefficient pullback in this statement.

Source: `sk-prop-diagonal-tower-trace.proof.md` (1), the identification of the
section class; `sk-lem-geo-p1-cohomology.proof.md`, Kummer normalization.
(blueprint: lem-sfb-finite-p1-kummer-chern-realization).

Proof: exact evaluation on single complexes and on shifts first identifies
Ev(line[2]) with the finite coefficient Tate line in degree minus two, using
lineEvaluation. The line section comparison in c identifies this line with
associated-module realization of the comparison pullback of the etale Tate
line. Pullback along e identifies that object with the pullback of the line
on P¹; these canonical comparisons construct t. The constant comparison is
finiteOverUnitCoordinate: it sends one to one, by c.unit_sections.
Apply hc to the Picard class e*O(1) and the level n. Its displayed boundary
equality says that, after forgetting scalars and precomposing with the
integral quotient, the evaluated Chern class is exactly the positive Kummer
boundary followed by z mapping to 1 tensor z. The normalized line comparison
c.line_sections identifies that root map with the etale scalar root map.
Exact site comparison commutes with the Kummer connecting morphism, and the
Picard pullback of O(1) along e is the same line bundle in both constructions.
The constants/scalar-extension adjunction identifies maps from the regular
coefficient unit with maps from the integral unit after scalar restriction;
hence this equality on the integral generator determines the original
coefficient-linear derived arrow. The finiteP1PositiveClass used here is the actual comparison image
of the etale Kummer class, independently of any pushforward. The proved
finiteP1PositiveClass_adjunct identifies its adjunct with the second
component of the decomposition. This proves the
displayed equality before direct image, without the inverse decomposition,
negative twists, or any cohomology-vanishing assertion. Trivial line bundles,
empty schemes and the zero ring are covered by the same natural maps. -/
theorem finiteP1_kummer_chern_realization
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (e : X ≅ ProjectiveLine S) (cX : Chern l E X)
    (hc : FiniteChernNormalization l E cX)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX) :
    ∃ t : (SpTowerShriek.Ev l E X n).obj ((line l E cX)⟦(2 : ℤ)⟧) ≅
      (finiteOverRealization l E n e).obj
        (geoP1Twist (FiniteRing l E n) (l ^ (n + 1))
          (ULift.ext (coefficient_annihilates l E n)) (ProjectiveLine S) 1 2),
      (SpTowerShriek.Ev l E X n).map
          (firstChern l E cX (Scheme.Pic.mapHom e.hom (hyperplanePic S))) ≫ t.hom =
        (finiteOverUnitCoordinate l E n e c).hom ≫
          (finiteOverRealization l E n e).map (finiteP1PositiveClass l E S hS n) := by
  let t := finiteP1KummerCoordinate l E n e cX hS c
  have hb : FiniteP1BoundaryData l E e cX n := by
    exact hc (Scheme.Pic.mapHom e.hom (hyperplanePic S)) n
  have h := finiteP1_kummer_chern_realization_of_boundary l E e cX hS n c t rfl hb
  exact ⟨t, by simpa only [finiteP1PositiveClass] using h⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
