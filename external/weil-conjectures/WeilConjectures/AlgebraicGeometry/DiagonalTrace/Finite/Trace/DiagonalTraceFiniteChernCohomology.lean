/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels

import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteChernComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The finite degree-two Chern generator

Source: blueprint latest, diagonal-tower trace proof (1), and projective-line
cohomology (G2). This is only the degree-two calculation for the second component.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

private theorem isIso_map_inr_of_isZero_left
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {U V : C} [HasBinaryBiproduct U V]
    (hU : IsZero (F.obj U)) : IsIso (F.map (biprod.inr : V ⟶ U ⊞ V)) := by
  have hzero : F.map (biprod.fst ≫ biprod.inl : U ⊞ V ⟶ U ⊞ V) = 0 := by
    rw [F.map_comp, hU.eq_of_src (F.map biprod.inl) 0, comp_zero]
  refine ⟨⟨F.map biprod.snd, ?_, ?_⟩⟩
  · rw [← F.map_comp, biprod.inr_snd, F.map_id]
  · have ht := congrArg F.map (biprod.total (X := U) (Y := V))
    rw [F.map_add, hzero, zero_add, F.map_id, F.map_comp] at ht
    exact ht

private theorem evaluation_reflects_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (S : Scheme.{u})
    {M N : SpTowerShriek.S l E S} (f : M ⟶ N)
    (hf : ∀ n : ℕ, IsIso ((SpTowerShriek.ev l E S n).map f)) : IsIso f := by
  let single := DerivedCategory.singleFunctor (SpTowerShriek.S l E S) 0
  have : IsIso (single.map f) := by
    apply (b.calculus S).detects
    intro n
    have := hf n
    exact (NatIso.isIso_map_iff
      ((SpTowerShriek.ev l E S n).mapDerivedCategorySingleFunctor 0) f).2
        (Functor.map_isIso (DerivedCategory.singleFunctor _ 0)
          ((SpTowerShriek.ev l E S n).map f))
  exact isIso_of_reflects_iso f single

/-- The actual untwisted Chern component induces the finite degree-two generator.

Source: `sk-prop-diagonal-tower-trace.proof.md` (1), and
`lemma-cohomology-projective-line-trace` (G2), the Chern summand.
(blueprint: lem-sfb-diagonal-trace-finite-chern-cohomology).

Proof: compare the positive Chern adjunct at each finite level with the second
component of the positively twisted ordinary decomposition (G2). The left
summand A(1)[2] has no H⁰. Additivity shows that its complementary second
injection is invertible on H⁰, so invertibility of (G2) gives invertibility
of H⁰ of the positive Chern adjunct. Exact scalar realization and the arrow
comparison carry this conclusion back to the evaluated tower adjunct.
Exact evaluation commutes with homology. To reflect isomorphisms of system
sheaves, place each map in degree zero and apply the derived evaluation
detector and the single/evaluation comparisons; full faithfulness of the
single functor then reflects invertibility. Hence H⁰ of the actual system
Chern adjunct is invertible. Compose with twistedPush inverse and the
positive-twist shift comparison, then apply the exact negative-twist
functor. Its homology comparison preserves invertibility on H⁰. Compose
with inverseUnit inverse and cancelNegative, shift by minus two and cancel
the shifts. This is precisely Model.second. The homology shift comparison
turns H⁰ before this shift into H² afterwards. Finally exact finite
evaluation preserves this H² isomorphism. This avoids all finite
negative-twist and tensor/Hom realization comparisons. The argument uses
positive exponents k+1, including k=0, and works for zero coefficients. -/
theorem diagonalTrace_finite_chern_cohomology
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    {b : SpTowerShriek.Base l E} {f : X ⟶ S}
    {cS : Chern l E S} {cX : Chern l E X}
    {tS : Twisting l E cS} {tX : Twisting l E cX}
    (m : Model l E b S X f cS cX tS tX)
    (hc : FiniteChernNormalization l E cX)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ) :
    IsIso ((DerivedCategory.homologyFunctor _ (2 : ℤ)).map
      ((SpTowerShriek.Ev l E S n).map (m.second l E))) := by
  let H₀ := DerivedCategory.homologyFunctor (SpTowerShriek.S l E S) (0 : ℤ)
  let H₂ := DerivedCategory.homologyFunctor (SpTowerShriek.S l E S) (2 : ℤ)
  have hchern : IsIso (H₀.map (m.chernAdjoint l E)) := by
    apply evaluation_reflects_iso l E b S
    intro k
    have : Finite (SpTowerShriek.R l E k) := b.finite k
    let A := FiniteRing l E k
    let hA : ((l ^ (k + 1) : ℕ) : A) = 0 :=
      ULift.ext (coefficient_annihilates l E k)
    let hNS : IsUnit ((l ^ (k + 1) : ℕ) : Γ(S, ⊤)) := by
      simpa only [Nat.cast_pow] using hS.pow (k + 1)
    let F := (Scheme.sfIntrinsicModuleEquivalence S (SpTowerShriek.R l E k)).functor
    let H := DerivedCategory.homologyFunctor
      (Scheme.proEtaleRingModules S (Scheme.proEtaleConstantRing S
        (SpTowerShriek.R l E k))) (0 : ℤ)
    let G := F.mapDerivedCategory ⋙ H
    let d := geoP1TwistedMap A (l ^ (k + 1))
      (pow_pos (Fact.out : l.Prime).pos _) hA S hNS
    obtain ⟨decomp, hd, _⟩ := geoP1Cohomology l (Fact.out : l.Prime) (k + 1)
      (Nat.succ_pos k) A hA
    have : IsIso d := by
      change IsIso (geoP1TwistedMap A _ _ hA S hNS)
      rw [← (hd S hNS).2]
      infer_instance
    have hz : IsZero (G.obj (geoP1Twist A (l ^ (k + 1)) hA S 1 2)) := by
      apply F.isZero_homologyFunctor_mapDerivedCategory_obj
      apply (comparisonUpperStar (ModuleCat.{u + 1} A) S
        ).isZero_homologyFunctor_mapDerivedCategory_obj
      have hline : (Etale.p1DecompositionTwist A (l ^ (k + 1)) hA S 1 2).IsLE (-2) :=
        DerivedCategory.TStructure.t.isLE_shift _ 0 2 (-2)
      exact DerivedCategory.isZero_of_isLE _ (-2) 0 (by decide) (hX := hline)
    have hinr := isIso_map_inr_of_isZero_left G (V := geoP1Unit A S) hz
    have hcomponent : IsIso (G.map (biprod.inr ≫ d)) := by
      rw [G.map_comp]
      infer_instance
    obtain ⟨a, v, hv⟩ := diagonalTrace_finite_chern_comparison l E b m.model m.over_eq
      m.geometry m.coefficientPullback cX hc hS k
    have hcomp : IsIso (H.map ((SpTowerShriek.Ev l E S k).map (m.chernAdjoint l E)) ≫
        H.map v.hom) := by
      change (SpTowerShriek.Ev l E S k).map (m.chernAdjoint l E) ≫ v.hom =
        a.hom ≫ F.mapDerivedCategory.map (biprod.inr ≫ d) at hv
      rw [← H.map_comp, hv, H.map_comp]
      exact IsIso.comp_isIso' (Functor.map_isIso H a.hom) hcomponent
    have hi : IsIso (H.map ((SpTowerShriek.Ev l E S k).map (m.chernAdjoint l E))) :=
      IsIso.of_isIso_comp_right _ (H.map v.hom)
    exact (NatIso.isIso_map_iff
      ((SpTowerShriek.ev l E S k).mapDerivedCategoryHomologyFunctorIso 0)
        (m.chernAdjoint l E)).2 hi
  let P := (SpTowerShriek.push l E b m.geometry).obj (unit X (Arings l E X))
  let g := m.chernAdjoint l E ≫ (m.twistedPush l E).inv ≫
    ((tS.T l E).commShiftIso (2 : ℤ)).inv.app P
  have hg : IsIso (H₀.map g) := by
    dsimp only [g]
    rw [H₀.map_comp, H₀.map_comp]
    infer_instance
  have hNg : IsIso (H₀.map ((tS.N l E).map g)) :=
    (NatIso.isIso_map_iff (tS.equivalence.inverse.mapDerivedCategoryHomologyFunctorIso 0)
      g).1 (Functor.map_isIso tS.equivalence.inverse (H₀.map g))
  let z := (tS.inverseUnit l E).inv ≫ (tS.N l E).map g ≫
    (tS.cancelNegative l E).hom.app (P⟦(2 : ℤ)⟧)
  have hz : IsIso (H₀.map z) := by
    dsimp only [z]
    rw [H₀.map_comp, H₀.map_comp]
    infer_instance
  have hshift : IsIso (H₂.map (z⟦(-2 : ℤ)⟧')) := by
    have hz' : IsIso ((H₀.shift (0 : ℤ)).map z) := by
      simpa only [H₀, DerivedCategory.shift_homologyFunctor] using hz
    have hs := (NatIso.isIso_map_iff (H₀.shiftIso (-2 : ℤ) 2 0 (by decide)) z).2 hz'
    simpa only [H₀, H₂, DerivedCategory.shift_homologyFunctor, Functor.comp_map] using hs
  have hsecond : IsIso (H₂.map (m.second l E)) := by
    change IsIso (H₂.map (z⟦(-2 : ℤ)⟧' ≫ _))
    rw [Functor.map_comp]
    infer_instance
  have hev : IsIso ((SpTowerShriek.ev l E S n).map (H₂.map (m.second l E))) := by
    exact Functor.map_isIso (SpTowerShriek.ev l E S n) (H₂.map (m.second l E))
  exact (NatIso.isIso_map_iff
    ((SpTowerShriek.ev l E S n).mapDerivedCategoryHomologyFunctorIso 2)
      (m.second l E)).1 hev

end AlgebraicGeometry.ProEtale.DiagonalTrace
