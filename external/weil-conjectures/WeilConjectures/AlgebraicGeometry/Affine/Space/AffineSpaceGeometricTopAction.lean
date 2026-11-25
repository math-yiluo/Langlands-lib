/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpacePolynomialDeformation
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearActionFamily
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearActionRigidity
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence
import WeilConjectures.SixFunctors.Etale.Derived.Exchange
import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift

/-! # The geometric top cohomology calculation for affine space -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriek affineLinearCompactComparison
  affineLinearCoefficientDescent affineLinearBaseCoefficient
  leftDerivedUpperStarComp derivedSquareUpperStarIso upperStar Functor.leftDerivedFunctor

private lemma pullback_id_eq (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    affineLinearPullbackId A S = leftDerivedUpperStarId (ModuleCat.{u + 1} A) S := by
  simp [affineLinearPullbackId, leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    leftDerivedUpperStarIsoMapDerivedCategory]

private lemma iso_diagram {C : Type*} [Category C]
    {O U V W P Q T R : C}
    (a : O ≅ U) (b : U ≅ V) (c : O ≅ W) (d : W ≅ V)
    (e : U ≅ P) (f : O ≅ Q) (g : Q ≅ P) (h : O ≅ T) (i : T ≅ R) (j : W ≅ R)
    (h1 : a.hom ≫ b.hom = c.hom ≫ d.hom)
    (h2 : a.hom ≫ e.hom = f.hom ≫ g.hom)
    (h3 : h.hom ≫ i.hom = c.hom ≫ j.hom) :
    b.inv ≫ e.hom ≫ g.inv = d.inv ≫ j.hom ≫ i.inv ≫ h.inv ≫ f.hom := by
  apply (cancel_epi (a.hom ≫ b.hom)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h2, Iso.hom_inv_id, Category.comp_id]
  rw [reassoc_of% h1, Iso.hom_inv_id_assoc, ← reassoc_of% h3]
  simp

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem descended_coefficient_square
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (v : X' ⟶ X) (g : Y' ⟶ Y)
    (a : X ⟶ X) (a' : X' ⟶ X')
    (hs : v ≫ p = p' ≫ g) (ha : a ≫ p = p) (ha' : a' ≫ p' = p')
    (hw : a' ≫ v = v ≫ a) (L : DerivedCategoryModule A Y) :
    (upperStar (ModuleCat.{u + 1} A) a').leftDerivedFunctor.map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk hs)).inv.app L) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a' p' p' ha'.symm).inv.app
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj L) =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk hw)).inv.app
        ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj L) ≫
      (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a p p ha.symm).inv.app L) ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk hs)).inv.app L := by
  have hd : v ≫ p = (a' ≫ v) ≫ p := by rw [hw, Category.assoc, ha]
  have A1 := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    a' v p (a' ≫ v) (v ≫ p) (v ≫ p) rfl rfl hd L
  have A2 := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    a' p' g p' (v ≫ p) (v ≫ p) ha'.symm hs hs L
  have A3 := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    v a p (a' ≫ v) p (v ≫ p) hw ha.symm hd L
  have h := iso_diagram
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a' (v ≫ p) (v ≫ p)
      (by rw [← Category.assoc, hw, Category.assoc, ha])).app L)
    ((upperStar (ModuleCat.{u + 1} A) a').leftDerivedFunctor.mapIso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).app L))
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (a' ≫ v) p (v ≫ p) hd).app L)
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a' v).app
      ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj L))
    ((upperStar (ModuleCat.{u + 1} A) a').leftDerivedFunctor.mapIso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p' g (v ≫ p) hs).app L))
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p' g (v ≫ p) hs).app L)
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a' p' p' ha'.symm).app
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj L))
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).app L)
    ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.mapIso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a p p ha.symm).app L))
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v a (a' ≫ v) hw).app
      ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj L)) A1 A2 A3
  simpa only [derivedSquareUpperStarIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.map_comp, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc] using h

attribute [local semireducible] affineLinearBaseCoefficient in
private def baseCoefficientPullback
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
    (ordinaryFinitePullback A f).obj (affineLinearBaseCoefficient A N hA Y d) ≅
      affineLinearBaseCoefficient A N hA X d :=
  Nat.rec (motive := fun e ↦
    (ordinaryFinitePullback A f).obj (affineLinearBaseCoefficient A N hA Y e) ≅
      affineLinearBaseCoefficient A N hA X e)
    (ordinaryFiniteUnitPullback A f)
    (fun e r ↦ ordinaryFiniteTensorPullback A f (affineLinearBaseCoefficient A N hA Y e)
        ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) ≪≫
      ordinaryFiniteTensorRightMapIso A X r
        (ordinaryFiniteShiftedLinePullback A N hA t f hY)) d

private def coefficientBaseChange
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S)
    (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤))) (d : ℕ) :
    (ordinaryFinitePullback A (affineTraceMap f d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅
      (affineTraceRight A N hA S' d).obj (ordinaryFiniteUnit A S') :=
  (ordinaryFinitePullback A (affineTraceMap f d)).mapIso
      (affineLinearCoefficientDescent A N hA t S hS d) ≪≫
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
      (affineTraceMap_isPullback f d).toCommSq).app
        (affineLinearBaseCoefficient A N hA S d)).symm ≪≫
    (ordinaryFinitePullback A (affineTraceProjection S' d)).mapIso
      (baseCoefficientPullback A N hA t f hS d) ≪≫
    (affineLinearCoefficientDescent A N hA t S' hS' d).symm

attribute [local irreducible] baseCoefficientPullback coefficientBaseChange

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem coefficientBaseChange_equivariant
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S)
    (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤))) (d : ℕ)
    (a : affineTraceTower S d ⟶ affineTraceTower S d)
    (a' : affineTraceTower S' d ⟶ affineTraceTower S' d)
    (ha : a ≫ affineTraceProjection S d = affineTraceProjection S d)
    (ha' : a' ≫ affineTraceProjection S' d = affineTraceProjection S' d)
    (hw : a' ≫ affineTraceMap f d = affineTraceMap f d ≫ a) :
    (ordinaryFinitePullback A a').map (coefficientBaseChange A N hA t f hS hS' d).hom ≫
        (affineLinearCoefficientPullback A N hA t S' hS' d a' ha').hom =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk hw)).inv.app _ ≫
        (ordinaryFinitePullback A (affineTraceMap f d)).map
          (affineLinearCoefficientPullback A N hA t S hS d a ha).hom ≫
        (coefficientBaseChange A N hA t f hS hS' d).hom := by
  have hr := descended_coefficient_square A
    (affineTraceProjection S d) (affineTraceProjection S' d)
    (affineTraceMap f d) f a a' (affineTraceMap_isPullback f d).w ha ha' hw
    (affineLinearBaseCoefficient A N hA S d)
  apply (cancel_mono (affineLinearCoefficientDescent A N hA t S' hS' d).hom).mp
  simp only [coefficientBaseChange, affineLinearCoefficientPullback,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  simp only [Iso.inv_hom_id, Category.comp_id, ← Functor.map_comp_assoc,
    Iso.inv_hom_id]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a'
    (affineTraceProjection S' d) (affineTraceProjection S' d) ha'.symm).inv.naturality
      (baseCoefficientPullback A N hA t f hS d).hom
  simp only [Functor.comp_map] at hn
  dsimp only [ordinaryFinitePullback] at hr hn ⊢
  rw [hn, reassoc_of% hr]
  have hsquare := (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
    (CommSq.mk hw)).inv.naturality
      (affineLinearCoefficientDescent A N hA t S hS d).hom
  simp only [Functor.comp_map] at hsquare
  erw [reassoc_of% hsquare]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem action_baseChange
    (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
    (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hS' : IsUnit (N : Γ(S', ⊤))) (d : ℕ)
    (a : affineTraceTower S d ⟶ affineTraceTower S d)
    (a' : affineTraceTower S' d ⟶ affineTraceTower S' d)
    (sa : IsPullback a (affineTraceProjection S d) (affineTraceProjection S d) (𝟙 S))
    (sa' : IsPullback a' (affineTraceProjection S' d) (affineTraceProjection S' d) (𝟙 S'))
    (hw : a' ≫ affineTraceMap f d = affineTraceMap f d ≫ a) :
    ∃ C : (ordinaryFinitePullback A f).obj
        ((affineTraceLeft A S d).obj
          ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))) ≅
        (affineTraceLeft A S' d).obj
          ((affineTraceRight A N hA S' d).obj (ordinaryFiniteUnit A S')),
      (ordinaryFinitePullback A f).map (affineLinearTraceAction N hN A hA t S hS d a sa) ≫
          C.hom =
        C.hom ≫ affineLinearTraceAction N hN A hA t S' hS' d a' sa' := by
  let := affineTraceNoetherian S d
  let := affineTraceNoetherian S' d
  let sq := affineTraceMap_isPullback f d
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  let B := (asIso (rightDerivedLowerShriekBaseChangeMap A sq)).app
    ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))
  let C := (ordinaryFinitePullback A f).mapIso
      (affineLinearCompactComparison N hN A hA S hS d) ≪≫ B ≪≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S' d)).mapIso (coefficientBaseChange A N hA t f hS hS' d) ≪≫
    (affineLinearCompactComparison N hN A hA S' hS' d).symm
  refine ⟨C, ?_⟩
  have he := affineLinearExchange_action_naturality A sq
    sa
    sa'
    hw
    ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))
    ((affineTraceRight A N hA S' d).obj (ordinaryFiniteUnit A S'))
    (affineLinearCoefficientPullback A N hA t S hS d _
      (sa.w.trans (Category.comp_id _))).hom
    (affineLinearCoefficientPullback A N hA t S' hS' d _
      (sa'.w.trans (Category.comp_id _))).hom
    (coefficientBaseChange A N hA t f hS hS' d).hom
    (coefficientBaseChange_equivariant A N hA t f hS hS' d _ _
      (sa.w.trans (Category.comp_id _))
      (sa'.w.trans (Category.comp_id _))
      hw)
  have h := congrArg (fun z ↦
    (ordinaryFinitePullback A f).map
      (affineLinearCompactComparison N hN A hA S hS d).hom ≫ z ≫
        (affineLinearCompactComparison N hN A hA S' hS' d).inv) he
  simp only [C, B, affineLinearTraceAction,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, pullback_id_eq]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id,
    Functor.map_comp, Iso.inv_hom_id_assoc]
  simpa only [Functor.map_comp, Category.assoc] using h

private theorem linear_action_id
    (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) :
    affineLinearTraceAction N hN A hA t S hS d (affineTraceLinearMap S d g)
      (affineTraceLinearMap_isPullback S d g) = 𝟙 _ := by
  have hcomp := affineLinearAction_family N hN A hA t S hS d
  let r := linearActionMatrix N hN A hA t (generalLinearOpen d S).toScheme
    (linearUniversalInvertible N S hS d) d (linearUniversalMatrix S d)
  have hid : (ordinaryFinitePullback A (glOne (c := d) (S := S))).map r = 𝟙 _ := by
    obtain ⟨C, hC⟩ := hcomp 1
    change (ordinaryFinitePullback A (glOne (c := d) (S := S))).map r ≫ C.hom = _ at hC
    rw [affineLinearAction_one, Category.comp_id] at hC
    apply (cancel_mono C.hom).mp
    simpa only [Category.id_comp] using hC
  have hr : r = 𝟙 _ :=
    linearAction_eq_id_of_identitySection N hN A hA S hS d r hid
  obtain ⟨C, hC⟩ := hcomp g
  change (ordinaryFinitePullback A _).map r ≫ C.hom = _ at hC
  rw [hr, CategoryTheory.Functor.map_id, Category.id_comp] at hC
  have hlin : linearActionMatrix N hN A hA t S hS d g = 𝟙 _ :=
    (cancel_epi C.hom).mp (hC.symm.trans (Category.comp_id C.hom).symm)
  exact hlin

private theorem line_zero_detects
    (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (r : (affineTraceLeft A (AffineSpace PUnit.{u + 1} S) d).obj
        ((affineTraceRight A N hA (AffineSpace PUnit.{u + 1} S) d).obj
          (ordinaryFiniteUnit A (AffineSpace PUnit.{u + 1} S))) ⟶
      (affineTraceLeft A (AffineSpace PUnit.{u + 1} S) d).obj
        ((affineTraceRight A N hA (AffineSpace PUnit.{u + 1} S) d).obj
          (ordinaryFiniteUnit A (AffineSpace PUnit.{u + 1} S))))
    (hr : (ordinaryFinitePullback A (AffineSpace.zeroSection PUnit.{u + 1} S)).map r =
      𝟙 _) : r = 𝟙 _ := by
  let P := AffineSpace PUnit.{u + 1} S
  let p := P ↘ S
  let z := AffineSpace.zeroSection PUnit.{u + 1} S
  let : IsNoetherian P := affineTraceNoetherian S 1
  obtain ⟨t₀, D₀, _, htrace⟩ := exists_affineSpaceTopTrace N hN A hA
  have := (htrace P (affineTraceInvertible N S hS 1) d).2.2.1
  let e := asIso (affineTraceCounit A N hA t₀ D₀ P
    (affineTraceInvertible N S hS 1) d)
  have hunit : DerivedCategory.isInvertible A P (ordinaryFiniteUnit A P) :=
    ⟨_, ⟨derivedTensorLeftUnitor _ _ _⟩, ⟨derivedTensorLeftUnitor _ _ _⟩⟩
  have hz : ∀ x : P, ∃ T : Set P, _root_.IsPreconnected T ∧ x ∈ T ∧
      (T ∩ Set.range z.base).Nonempty := by
    intro x
    have hp : z ≫ p = 𝟙 S := AffineSpace.zeroSection_comp_over _ _
    refine ⟨p.base ⁻¹' {p.base x}, ?_, rfl, z.base (p.base x), ?_, p.base x, rfl⟩
    · exact (p.isIrreducible_preimage (AffineSpace.isOpenMap_over S)
        isIrreducible_singleton).isPreirreducible.isPreconnected
    · simpa using congrArg (fun f : S ⟶ S ↦ f.base (p.base x)) hp
  exact eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible z hz
    (DerivedCategory.isInvertible.of_iso e.symm hunit) r hr

/-- An automorphism over an algebraically closed field fixes the degree-zero homology
of the shifted, twisted compact-support object of affine space.

Source: latest blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-affine-space-geometric-top-action).

Proof: use the polynomial family H(t,x)=(e(tx)-e(0))/t+t*e(0), with
polynomial inverse as described in affineSpace_polynomial_deformation. Its fibre
at zero is an invertible linear map, and its fibre at one is e. The ordered trace
identifies the compact-support source over the parameter line with the constant
complex; in particular this source is tensor-invertible. Every point of the line
lies in a preconnected fibre of the projection meeting the closed zero section.
Thus the existing identity detector for invertible complexes detects the identity
on the zero section. The universal linear action specializes to the identity at
its identity section, so rigidity on the general linear group makes every linear
action the identity. Exchange pasting and coherence of coefficient descent show
that pulling the family action back along either endpoint conjugates it to the
corresponding endpoint action. The zero endpoint therefore detects that the family
action is identity; the one endpoint gives that e acts as identity. Apply the
homology functor. This proves identity of the actual derived endomorphism before
passing to homology; no general faithfulness of derived pullback is used. Dimension
zero and the zero coefficient ring satisfy the same argument.
-/
theorem affineSpaceIsoTraceAction_homology_zero
    (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (k : Type u) [Field k] [IsAlgClosed k]
    (hk : IsUnit (N : Γ(Spec (.of k), ⊤))) (d : ℕ)
    (e : affineTraceTower (Spec (.of k)) d ≅ affineTraceTower (Spec (.of k)) d)
    (sq : IsPullback e.hom (affineTraceProjection (Spec (.of k)) d)
      (affineTraceProjection (Spec (.of k)) d) (𝟙 (Spec (.of k)))) :
    (_root_.DerivedCategory.homologyFunctor
      (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} A)) 0).map
        (affineLinearTraceAction N hN A hA t (Spec (.of k)) hk d e.hom sq) = 𝟙 _ := by
  let S := Spec (.of k)
  let P := AffineSpace PUnit.{u + 1} S
  let : IsNoetherian P := affineTraceNoetherian S 1
  let hP := affineTraceInvertible N S hk 1
  obtain ⟨g, E, hE, hzero, hone⟩ := affineSpace_polynomial_deformation k d e
    (sq.w.trans (Category.comp_id _))
  let sE : IsPullback E.hom (affineTraceProjection P d)
      (affineTraceProjection P d) (𝟙 P) :=
    IsPullback.of_horiz_isIso ⟨by simpa using hE⟩
  let r := affineLinearTraceAction N hN A hA t P hP d E.hom sE
  obtain ⟨C₀, hC₀⟩ := action_baseChange N hN A hA t
    (AffineSpace.zeroSection PUnit.{u + 1} S) hP hk d E.hom
    (affineTraceLinearMap S d g) sE (affineTraceLinearMap_isPullback S d g) hzero.symm
  have h₀ : (ordinaryFinitePullback A
      (AffineSpace.zeroSection PUnit.{u + 1} S)).map r = 𝟙 _ := by
    rw [linear_action_id N hN A hA t S hk d g, Category.comp_id] at hC₀
    exact (cancel_mono C₀.hom).mp (by simpa only [Category.id_comp] using hC₀)
  have hr : r = 𝟙 _ := line_zero_detects N hN A hA S hk d r h₀
  obtain ⟨C₁, hC₁⟩ := action_baseChange N hN A hA t
    (AffineSpace.oneSection PUnit.{u + 1} S) hP hk d E.hom e.hom sE sq hone.symm
  change (ordinaryFinitePullback A _).map r ≫ C₁.hom = _ at hC₁
  rw [hr, CategoryTheory.Functor.map_id, Category.id_comp] at hC₁
  have he : affineLinearTraceAction N hN A hA t S hk d e.hom sq = 𝟙 _ :=
    (cancel_epi C₁.hom).mp (by simpa only [Category.comp_id] using hC₁.symm)
  rw [he, CategoryTheory.Functor.map_id]

end AlgebraicGeometry.Etale
