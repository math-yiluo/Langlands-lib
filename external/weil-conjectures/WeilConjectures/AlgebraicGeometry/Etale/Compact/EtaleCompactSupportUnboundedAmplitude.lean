/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeGeometryFibreBound
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.Proper.ProperDerivedDirectImageCoproducts
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBoundedBelow
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence
import Mathlib.RingTheory.KrullDimension.Field

/-! # Unbounded amplitude and coproducts of finite etale compact supports

Source: Zheng, Six operations and Lefschetz-Verdier formula for Deligne-Mumford stacks,
Corollary 2.19, printed p. 12, and the coproduct argument of Proposition 2.23
(blueprint: lem-pur-etale-support-unbounded-amplitude).

The functor below is the existing ordinary unbounded `Rr_*` after the exact derived
extension by zero for the supplied compactification, not a new compact-support construction.
The geometric bound is asserted before quantifying over coefficient rings.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [-instance] commShiftRightDerivedLowerStar isTriangulated_rightDerivedLowerStar in
/-- Finite prime-to-characteristic etale compact support is triangulated, preserves
set-indexed coproducts, and has unbounded amplitude in `[0, 2d]` for every bound `d` on
geometric fibres of the original morphism. All three schemes are Noetherian, quasi-compact
and quasi-separated, without any separatedness hypothesis on either structure morphism.

Source: Zheng, Corollary 2.19, printed p. 12; Proposition 2.23, coproduct argument
(blueprint: lem-pur-etale-support-unbounded-amplitude).

Proof:
1. Finite type over the Noetherian point gives local Noetherianity and compactness.
   Properness gives these for the ambient scheme. Apply the finite-type geometry lemma
   to Y over Spec k, and then to f, obtaining a coefficient-independent fibre bound.
2. Both factors of Rr_* Dj_! are triangulated. The derived adjunction Dj_! ⊣ Dj^*
   gives coproduct preservation for the first factor in every indexing universe;
   proper derived direct image preserves coproducts for the second factor.
3. Exact extension by zero preserves the lower t-bound, and derived direct image is
   left t-exact. Thus F preserves every lower t-bound.
4. The coefficient exponent is invertible on Y. Compare the supplied compactification
   with the one used by the heart amplitude theorem on bounded-below objects. Together
   with step 3 this bounds F on the entire heart in [0,2d]. Bounded-heart devissage
   then bounds F on every bounded interval.
5. The existing uniform unbounded upper-amplitude theorem gives some N with
   F(D^{≤v}) contained in D^{≤v+N}; N need not equal 2d. Given K in D^{≤a}, put
   m = min(a,a+2d-N) and use the triangle τ_{<m}K -> K -> τ_{≥m}K.
   Its first image is bounded by m-1+N ≤ a+2d. Its third term is bounded in [m,a],
   so step 4 bounds its image by a+2d. Closure of D^{≤a+2d} under extensions bounds FK.
6. Combine the upper and lower bounds. The argument applies to zero objects, empty
   schemes, the zero coefficient ring and d=0 without any nonemptiness assumption.

The uniform auxiliary bound is Stacks Project, more-etale.tex,
lemma-derived-lower-shriek-bounded, (3), for torsion coefficients; only its already
proved source-library implementation is used. No sharp bound on compactified fibres
is asserted. -/
theorem compactSupport_unbounded_amplitude
    (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (l : ℕ) [Fact l.Prime] (hlp : l ≠ p)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    (IsNoetherian X ∧ CompactSpace X ∧ QuasiSeparatedSpace X) ∧
    (IsNoetherian Y ∧ CompactSpace Y ∧ QuasiSeparatedSpace Y) ∧
    (IsNoetherian c.Z ∧ CompactSpace c.Z ∧ QuasiSeparatedSpace c.Z) ∧
    (∃ d : ℕ, ∀ y : Y, topologicalKrullDim
      (↑(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y))) ≤ (d : WithBot ℕ∞)) ∧
    ∀ (C : Type (u + 1)) [CommRing C] [Finite C],
      (∃ s : ℕ, (l ^ s : ℕ) • (1 : C) = 0) →
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).IsTriangulated ∧
      (∀ I : Type w, PreservesColimitsOfShape (Discrete I)
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c)) ∧
      (∀ (b : ℤ) (K : DerivedCategoryModule C X), _root_.DerivedCategory.IsGE K b →
        _root_.DerivedCategory.IsGE
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K) b) ∧
      ∀ d : ℕ,
        (∀ y : Y, topologicalKrullDim
          (↑(pullback f (Spec.map (CommRingCat.ofHom
            (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
              Y.fromSpecResidueField y))) ≤ (d : WithBot ℕ∞)) →
        (∀ (a : ℤ) (K : DerivedCategoryModule C X), _root_.DerivedCategory.IsLE K a →
          _root_.DerivedCategory.IsLE
            ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K)
            (a + 2 * (d : ℤ))) ∧
        (∀ (a b : ℤ), a ≤ b → ∀ K : DerivedCategoryModule C X,
          _root_.DerivedCategory.IsGE K a → _root_.DerivedCategory.IsLE K b →
          _root_.DerivedCategory.IsGE
            ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K) a ∧
          _root_.DerivedCategory.IsLE
            ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K)
            (b + 2 * (d : ℤ))) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of k))
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian X := ⟨⟩
  have : IsNoetherian Y := ⟨⟩
  have : IsNoetherian c.Z := ⟨⟩
  have hcover : ∃ (n : ℕ) (U : Fin n → (Spec (.of k)).affineOpens),
      (⨆ i, (U i).1) = ⊤ ∧ ∀ i, IsNoetherianRing Γ(Spec (.of k), (U i).1) := by
    refine ⟨1, fun _ ↦ ⟨⊤, isAffineOpen_top _⟩, by simp, ?_⟩
    intro i
    exact IsLocallyNoetherian.component_noetherian _
  have hdim : ∃ d : ℕ, topologicalKrullDim (Spec (.of k)) ≤ (d : WithBot ℕ∞) := by
    refine ⟨0, ?_⟩
    change topologicalKrullDim (PrimeSpectrum k) ≤ _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
    simp
  obtain ⟨hYcover, hYdim, -⟩ :=
    finiteType_noetherianCover_dimension_geometricFibres (Y ↘ Spec (.of k)) hcover hdim
  obtain ⟨_, _, ⟨d, hd⟩, _⟩ :=
    finiteType_noetherianCover_dimension_geometricFibres f hYcover hYdim
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance, inferInstance⟩, ⟨d, fun y ↦ hd _ _⟩, ?_⟩
  intro C _ _ hC
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c
  have hcop (I : Type w) : PreservesColimitsOfShape (Discrete I) F := by
    have : PreservesColimitsOfShape (Discrete I)
        (openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory :=
      (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} C) c.i).leftAdjoint_preservesColimits.preservesColimitsOfShape
    have := (proper_rightDerivedLowerStar_preservesCoproducts C c.g).1 I
    exact inferInstanceAs (PreservesColimitsOfShape (Discrete I)
      ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory ⋙
        rightDerivedLowerStar (ModuleCat.{u + 1} C) c.g))
  have hge (b : ℤ) (K : DerivedCategoryModule C X) (hK : K.IsGE b) :
      (F.obj K).IsGE b := by
    have := (openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).isGE_mapDerivedCategory_obj
      K b
    exact (lowerStar (ModuleCat.{u + 1} C) c.g).isGE_rightDerivedFunctor_obj _ b
  have htri : F.IsTriangulated := inferInstanceAs
    (((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory ⋙
      (lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor).IsTriangulated)
  refine ⟨htri, hcop, hge, ?_⟩
  obtain ⟨s, hs⟩ := hC
  have hlk : (l : k) ≠ 0 := by
    intro hzero
    have hdiv := (CharP.cast_eq_zero_iff k p l).mp hzero
    rcases (Nat.dvd_prime (Fact.out : l.Prime)).mp hdiv with hpone | hpl
    · exact ((CharP.char_is_prime_or_zero k p).resolve_right (Nat.ne_of_gt hp)).ne_one hpone
    · exact hlp hpl.symm
  have : HasInvertibleExponent C (Spec (.of k)) := by
    refine ⟨l ^ s, pow_pos (Nat.Prime.pos (Fact.out : l.Prime)) s, ?_, ?_⟩
    · simpa only [nsmul_eq_mul, mul_one] using hs
    · simpa only [map_pow, map_natCast, Nat.cast_pow] using
        ((Ne.isUnit hlk).pow s).map (Scheme.ΓSpecIso (.of k)).inv.hom
  have : HasInvertibleExponent C Y := .of_hom (Y ↘ Spec (.of k))
  intro d hd
  have hheart (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)) (q : ℤ)
      (hq : q < 0 ∨ 2 * (d : ℤ) < q) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (F.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj M))) := by
    rcases hq with hq | hq
    · have := hge 0 ((_root_.DerivedCategory.singleFunctor _ 0).obj M) inferInstance
      exact _root_.DerivedCategory.isZero_of_isGE _ 0 q hq
    · have hz := isZero_homology_rightDerivedLowerShriek_of_geometricFiberDimensionLE
        k C X Y f d hd M q hq
      exact hz.of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
        ((rightDerivedLowerShriekOfCompactificationPlusιIso C c
          (compactSupportAmplitudeCompactification k Y f)).app
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M)))
  obtain ⟨N, hN⟩ := exists_isLE_rightDerivedLowerShriekOfCompactification_obj C c
  have hle (a : ℤ) (K : DerivedCategoryModule C X) (hK : K.IsLE a) :
      (F.obj K).IsLE (a + 2 * (d : ℤ)) := by
    let m : ℤ := min a (a + 2 * (d : ℤ) - N)
    let T := (_root_.DerivedCategory.TStructure.t.triangleLTGE m).obj K
    have hT := F.map_distinguished T
      (_root_.DerivedCategory.TStructure.t.triangleLTGE_distinguished m K)
    have hleft : (F.obj T.obj₁).IsLE (a + 2 * (d : ℤ)) := by
      have h := hN T.obj₁ (m - 1) (by
        exact inferInstanceAs (_root_.DerivedCategory.TStructure.t.IsLE
          ((_root_.DerivedCategory.TStructure.t.truncLT m).obj K) (m - 1)))
      exact _root_.DerivedCategory.TStructure.t.isLE_of_le _ (m - 1 + N) _ (by
        dsimp [m]
        omega)
    have hright : (F.obj T.obj₃).IsLE (a + 2 * (d : ℤ)) := by
      have hGE : T.obj₃.IsGE m :=
        inferInstanceAs (_root_.DerivedCategory.TStructure.t.IsGE
          ((_root_.DerivedCategory.TStructure.t.truncGE m).obj K) m)
      have hLE : T.obj₃.IsLE a :=
        inferInstanceAs (_root_.DerivedCategory.TStructure.t.IsLE
          ((_root_.DerivedCategory.TStructure.t.truncGE m).obj K) a)
      apply (_root_.DerivedCategory.isLE_iff _ _).2
      intro i hi
      exact _root_.DerivedCategory.bounded_heart_amplitude _ _ F
        (fun _ ↦ True) (fun _ _ _ _ ↦ trivial) trivial 0 (2 * (d : ℤ)) (by omega)
        (fun M _ q hq ↦ hheart M q hq) m a (by dsimp [m]; omega) T.obj₃
        (fun r hr ↦ by
          rcases hr with hr | hr
          · exact _root_.DerivedCategory.isZero_of_isGE _ m r hr
          · exact _root_.DerivedCategory.isZero_of_isLE _ a r hr)
        (fun _ ↦ trivial) i (Or.inr hi)
    exact _root_.DerivedCategory.TStructure.t.isLE₂ _ hT _ hleft hright
  exact ⟨hle, fun a b _ K hKa hKb ↦ ⟨hge a K hKa, hle b K hKb⟩⟩

end AlgebraicGeometry.Etale
