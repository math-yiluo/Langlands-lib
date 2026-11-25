/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CohomologyFractionPresentation
public import Mathlib.Algebra.Exact.Basic
import WeilConjectures.AlgebraicGeometry.CohomologyFractionEventuallyZero

/-! # Exact Mayer--Vietoris row of fractions

Source: Stacks Project, Tag 09MR, Mayer--Vietoris paragraph.
(blueprint: lem-sc-cohomology-fraction-mayer-vietoris-exact)
-/

@[expose] public section

universe uMV

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry

private noncomputable def fractionOf {X : Scheme.{uMV}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (p : ℕ) (W : X.Opens) (n : ℕ) :
    (openModuleCohomology X.toRingedSpace p W).obj (F ⊗ L.tensorPow n : X.Modules) →+
      CohomologyFractionPresentation L F s p W :=
  (QuotientAddGroup.mk' _).comp (DirectSum.of (fun i : ℕ =>
    (openModuleCohomology X.toRingedSpace p W).obj (F ⊗ L.tensorPow i : X.Modules)) n)

private lemma fraction_zero {X : Scheme.{uMV}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (p : ℕ) (W : X.Opens) (n : ℕ) :
    cohomologyFraction L F s p W n 0 = 0 :=
  (fractionOf L F s p W n).map_zero

private lemma fraction_neg {X : Scheme.{uMV}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (p : ℕ) (W : X.Opens) (n : ℕ)
    (ξ : (openModuleCohomology X.toRingedSpace p W).obj
      (F ⊗ L.tensorPow n : X.Modules)) :
    cohomologyFraction L F s p W n (-ξ) = -cohomologyFraction L F s p W n ξ :=
  (fractionOf L F s p W n).map_neg ξ

private lemma fraction_transition {X : Scheme.{uMV}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (p : ℕ) (W : X.Opens) (n b : ℕ)
    (ξ : (openModuleCohomology X.toRingedSpace p W).obj
      (F ⊗ L.tensorPow n : X.Modules)) :
    cohomologyFraction L F s p W n ξ = cohomologyFraction L F s p W (n + b)
      ((openModuleCohomology X.toRingedSpace p W).map
        (mulTensorPowSection (homOfGlobalSection L s) F n b) ξ) := by
  apply sub_eq_zero.mp
  change QuotientAddGroup.mk' (cohomologyFractionRelations L F s p W) _ -
    QuotientAddGroup.mk' (cohomologyFractionRelations L F s p W) _ = 0
  rw [← map_sub]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply AddSubgroup.subset_closure
  exact ⟨n, b, ξ, rfl⟩

private lemma fraction_raise {X : Scheme.{uMV}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (p : ℕ) (W : X.Opens) (n k : ℕ) (h : n ≤ k)
    (ξ : (openModuleCohomology X.toRingedSpace p W).obj
      (F ⊗ L.tensorPow n : X.Modules)) :
    ∃ η, cohomologyFraction L F s p W n ξ = cohomologyFraction L F s p W k η := by
  have H : ∃ η, cohomologyFraction L F s p W n ξ =
      cohomologyFraction L F s p W (n + (k - n)) η :=
    ⟨_, fraction_transition L F s p W n (k - n) ξ⟩
  exact (Nat.add_sub_of_le h) ▸ H

private lemma fraction_exists {X : Scheme.{uMV}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (p : ℕ) (W : X.Opens)
    (x : CohomologyFractionPresentation L F s p W) :
    ∃ n ξ, x = cohomologyFraction L F s p W n ξ := by
  classical
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    induction x using DirectSum.induction_on with
    | zero => exact ⟨0, 0, (fractionOf L F s p W 0).map_zero.symm⟩
    | of n ξ => exact ⟨n, ξ, rfl⟩
    | add x y hx hy =>
      obtain ⟨n, ξ, hx⟩ := hx
      obtain ⟨m, η, hy⟩ := hy
      obtain ⟨ξ', hξ⟩ := fraction_raise L F s p W n (n + m) (Nat.le_add_right n m) ξ
      obtain ⟨η', hη⟩ := fraction_raise L F s p W m (n + m) (Nat.le_add_left m n) η
      change ∃ k ζ, QuotientAddGroup.mk' _ (x + y) = cohomologyFraction L F s p W k ζ
      rw [map_add]
      change ∃ k ζ, (QuotientAddGroup.mk x : CohomologyFractionPresentation L F s p W) +
        QuotientAddGroup.mk y = cohomologyFraction L F s p W k ζ
      rw [hx, hy, hξ, hη]
      exact ⟨n + m, _, (fractionOf L F s p W (n + m)).map_add _ _ |>.symm⟩

private lemma fraction_pair_exists {X : Scheme.{uMV}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (p q : ℕ) (W Z : X.Opens)
    (x : CohomologyFractionPresentation L F s p W)
    (y : CohomologyFractionPresentation L F s q Z) :
    ∃ n ξ η, x = cohomologyFraction L F s p W n ξ ∧
      y = cohomologyFraction L F s q Z n η := by
  obtain ⟨n, ξ, rfl⟩ := fraction_exists L F s p W x
  obtain ⟨m, η, rfl⟩ := fraction_exists L F s q Z y
  obtain ⟨ξ', hξ⟩ := fraction_raise L F s p W n (n + m) (Nat.le_add_right n m) ξ
  obtain ⟨η', hη⟩ := fraction_raise L F s q Z m (n + m) (Nat.le_add_left m n) η
  exact ⟨n + m, ξ', η', hξ, hη⟩

private lemma fraction_map_exists {X : Scheme.{uMV}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (p q : ℕ) (W Z : X.Opens)
    (t : openModuleCohomology X.toRingedSpace p W ⟶
      openModuleCohomology X.toRingedSpace q Z) :
    ∃ f : CohomologyFractionPresentation L F s p W →+
      CohomologyFractionPresentation L F s q Z,
      ∀ n ξ, f (cohomologyFraction L F s p W n ξ) =
        cohomologyFraction L F s q Z n (t.app (F ⊗ L.tensorPow n : X.Modules) ξ) := by
  classical
  let g := DirectSum.toAddMonoid fun n =>
    (fractionOf L F s q Z n).comp (t.app (F ⊗ L.tensorPow n : X.Modules)).hom
  have hg : cohomologyFractionRelations L F s p W ≤ g.ker := by
    unfold cohomologyFractionRelations
    apply (AddSubgroup.closure_le _).mpr
    rintro z ⟨n, b, ξ, rfl⟩
    change g (_ - _) = 0
    simp only [map_sub, g, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
    apply sub_eq_zero.mpr
    rw [show (fractionOf L F s q Z n) _ = cohomologyFraction L F s q Z n _ from rfl]
    rw [fraction_transition L F s q Z n b]
    congr 1
    exact (ConcreteCategory.congr_hom
      (t.naturality (mulTensorPowSection (homOfGlobalSection L s) F n b)) ξ).symm
  refine ⟨QuotientAddGroup.lift _ g hg, ?_⟩
  intro n ξ
  simp only [cohomologyFraction, QuotientAddGroup.lift_mk', g,
    DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
  rfl

private lemma fraction_naturality {X : Scheme.{uMV}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (p q : ℕ) (W Z : X.Opens)
    (t : openModuleCohomology X.toRingedSpace p W ⟶
      openModuleCohomology X.toRingedSpace q Z) (n b : ℕ)
    (ξ : (openModuleCohomology X.toRingedSpace p W).obj
      (F ⊗ L.tensorPow n : X.Modules)) :
    t.app (F ⊗ L.tensorPow (n + b) : X.Modules)
        ((openModuleCohomology X.toRingedSpace p W).map
          (mulTensorPowSection (homOfGlobalSection L s) F n b) ξ) =
      (openModuleCohomology X.toRingedSpace q Z).map
        (mulTensorPowSection (homOfGlobalSection L s) F n b)
        (t.app (F ⊗ L.tensorPow n : X.Modules) ξ) :=
  ConcreteCategory.congr_hom
    (t.naturality (mulTensorPowSection (homOfGlobalSection L s) F n b)) ξ

private lemma fraction_kill_pair {X : Scheme.{uMV}} (L F : X.Modules)
    [L.IsInvertible] (s : Γ(L, ⊤)) (p q r : ℕ) (W Z T : X.Opens)
    (t : openModuleCohomology X.toRingedSpace p W ⟶
      openModuleCohomology X.toRingedSpace q Z)
    (v : openModuleCohomology X.toRingedSpace p W ⟶
      openModuleCohomology X.toRingedSpace r T) (n : ℕ)
    (ξ : (openModuleCohomology X.toRingedSpace p W).obj
      (F ⊗ L.tensorPow n : X.Modules))
    (ht : cohomologyFraction L F s q Z n (t.app _ ξ) = 0)
    (hv : cohomologyFraction L F s r T n (v.app _ ξ) = 0) :
    ∃ k ζ, cohomologyFraction L F s p W n ξ = cohomologyFraction L F s p W k ζ ∧
      t.app (F ⊗ L.tensorPow k : X.Modules) ζ = 0 ∧
      v.app (F ⊗ L.tensorPow k : X.Modules) ζ = 0 := by
  obtain ⟨b, hb⟩ := cohomologyFraction_eventually_zero L F s q Z n _ ht
  let ξ' := (openModuleCohomology X.toRingedSpace p W).map
    (mulTensorPowSection (homOfGlobalSection L s) F n b) ξ
  have ht' : t.app (F ⊗ L.tensorPow (n + b) : X.Modules) ξ' = 0 := by
    dsimp only [ξ']
    rw [fraction_naturality, hb]
  have hv' : cohomologyFraction L F s r T (n + b)
      (v.app (F ⊗ L.tensorPow (n + b) : X.Modules) ξ') = 0 := by
    dsimp only [ξ']
    rw [fraction_naturality, ← fraction_transition, hv]
  obtain ⟨c, hc⟩ := cohomologyFraction_eventually_zero L F s r T (n + b) _ hv'
  let ζ := (openModuleCohomology X.toRingedSpace p W).map
    (mulTensorPowSection (homOfGlobalSection L s) F (n + b) c) ξ'
  refine ⟨n + b + c, ζ, ?_, ?_, ?_⟩
  · exact (fraction_transition L F s p W n b ξ).trans
      (fraction_transition L F s p W (n + b) c ξ')
  · dsimp only [ζ]
    rw [fraction_naturality, ht', map_zero]
  · dsimp only [ζ]
    rw [fraction_naturality, hc]

/-- An exact module-natural Mayer--Vietoris family induces an exact sequence on
cohomology fractions, with the prescribed restriction, difference, and boundary formulas.
This statement concerns only the upper row: it has no nonvanishing open or comparison map.

Source: Stacks Project, Tag 09MR, Mayer--Vietoris paragraph; Tag 01EB.
Proof: Apply the given family to every nonnegative twist F tensor L^n. Naturality
of its connecting transformations and of cohomology restriction makes the maps commute
with every transition multiplication by s^b. Extend each map to direct sums; the
fraction relations are preserved, so quotient descent gives a, b, and d, and the four
formulas follow on generators. The fraction presentation is the sequential direct
limit of these twists: finite sums can be moved to a common denominator, and zero
means zero after some further transition. For a class in a kernel, represent it at
one denominator and increase that denominator until its image is zero. Exactness of
the twist at that denominator supplies a preimage. Its fraction gives the required
preimage in the quotient. Conversely composites vanish at each twist and hence on
fractions. If a degree-zero class maps to zero, increase its denominator to make both
restrictions zero; injectivity at that twist makes the numerator zero. This proves
injectivity of a 0 as well. Neither compactness nor quasi-coherence is needed.
(blueprint: lem-sc-cohomology-fraction-mayer-vietoris-exact). -/
theorem exists_cohomologyFraction_mayerVietoris_exact (X : Scheme.{uMV})
    (L F : X.Modules) [L.IsInvertible]
    (s : Γ(L, ⊤))
    (U V : X.Opens) (δ : ∀ (A B : X.Opens) (p : ℕ),
      openModuleCohomology X.toRingedSpace p (A ⊓ B) ⟶
        openModuleCohomology X.toRingedSpace (p + 1) (A ⊔ B))
    (_hinj :
      (∀ (A B : X.Opens) (G : X.Modules),
        Function.Injective
          (fun x : (openModuleCohomology X.toRingedSpace 0 (A ⊔ B)).obj G =>
            ((openModuleCohomologyRestriction X.toRingedSpace 0
                (homOfLE (le_sup_left : A ≤ A ⊔ B))).app G x,
              (openModuleCohomologyRestriction X.toRingedSpace 0
                (homOfLE (le_sup_right : B ≤ A ⊔ B))).app G x))))
    (_hexact :
      (∀ (A B : X.Opens) (G : X.Modules) (p : ℕ),
        Function.Exact
          (fun x : (openModuleCohomology X.toRingedSpace p (A ⊔ B)).obj G =>
            ((openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (le_sup_left : A ≤ A ⊔ B))).app G x,
              (openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (le_sup_right : B ≤ A ⊔ B))).app G x))
          (fun x : (openModuleCohomology X.toRingedSpace p A).obj G ×
              (openModuleCohomology X.toRingedSpace p B).obj G =>
            (openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (inf_le_left : A ⊓ B ≤ A))).app G x.1 -
              (openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (inf_le_right : A ⊓ B ≤ B))).app G x.2) ∧
        Function.Exact
          (fun x : (openModuleCohomology X.toRingedSpace p A).obj G ×
              (openModuleCohomology X.toRingedSpace p B).obj G =>
            (openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (inf_le_left : A ⊓ B ≤ A))).app G x.1 -
              (openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (inf_le_right : A ⊓ B ≤ B))).app G x.2)
          ((δ A B p).app G) ∧
        Function.Exact ((δ A B p).app G)
          (fun x : (openModuleCohomology X.toRingedSpace (p + 1) (A ⊔ B)).obj G =>
            ((openModuleCohomologyRestriction X.toRingedSpace (p + 1)
                (homOfLE (le_sup_left : A ≤ A ⊔ B))).app G x,
              (openModuleCohomologyRestriction X.toRingedSpace (p + 1)
                (homOfLE (le_sup_right : B ≤ A ⊔ B))).app G x)))) :
    ∃ (a : ∀ p : ℕ, CohomologyFractionPresentation L F s p (U ⊔ V) →+
        CohomologyFractionPresentation L F s p U × CohomologyFractionPresentation L F s p V)
      (b : ∀ p : ℕ,
        CohomologyFractionPresentation L F s p U × CohomologyFractionPresentation L F s p V →+
          CohomologyFractionPresentation L F s p (U ⊓ V))
      (d : ∀ p : ℕ, CohomologyFractionPresentation L F s p (U ⊓ V) →+
        CohomologyFractionPresentation L F s (p + 1) (U ⊔ V)),
      (∀ (p n : ℕ) (ξ : (openModuleCohomology X.toRingedSpace p (U ⊔ V)).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        a p (cohomologyFraction L F s p (U ⊔ V) n ξ) =
          (cohomologyFraction L F s p U n
            ((openModuleCohomologyRestriction X.toRingedSpace p
              (homOfLE le_sup_left)).app (F ⊗ L.tensorPow n : X.Modules) ξ),
          cohomologyFraction L F s p V n
            ((openModuleCohomologyRestriction X.toRingedSpace p
              (homOfLE le_sup_right)).app (F ⊗ L.tensorPow n : X.Modules) ξ))) ∧
      (∀ (p n : ℕ)
        (ξ : (openModuleCohomology X.toRingedSpace p U).obj (F ⊗ L.tensorPow n : X.Modules)),
        b p (cohomologyFraction L F s p U n ξ, 0) = cohomologyFraction L F s p (U ⊓ V) n
          ((openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE inf_le_left)).app (F ⊗ L.tensorPow n : X.Modules) ξ)) ∧
      (∀ (p n : ℕ)
        (ξ : (openModuleCohomology X.toRingedSpace p V).obj (F ⊗ L.tensorPow n : X.Modules)),
        b p (0, cohomologyFraction L F s p V n ξ) = -cohomologyFraction L F s p (U ⊓ V) n
          ((openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE inf_le_right)).app (F ⊗ L.tensorPow n : X.Modules) ξ)) ∧
      (∀ (p n : ℕ) (ξ : (openModuleCohomology X.toRingedSpace p (U ⊓ V)).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        d p (cohomologyFraction L F s p (U ⊓ V) n ξ) =
          cohomologyFraction L F s (p + 1) (U ⊔ V) n
            ((δ U V p).app (F ⊗ L.tensorPow n : X.Modules) ξ)) ∧
      Function.Injective (a 0) ∧
      (∀ p : ℕ, Function.Exact (a p) (b p) ∧ Function.Exact (b p) (d p) ∧
        Function.Exact (d p) (a (p + 1))) := by
  classical
  let rU (p : ℕ) := openModuleCohomologyRestriction X.toRingedSpace p
    (homOfLE (le_sup_left : U ≤ U ⊔ V))
  let rV (p : ℕ) := openModuleCohomologyRestriction X.toRingedSpace p
    (homOfLE (le_sup_right : V ≤ U ⊔ V))
  let iU (p : ℕ) := openModuleCohomologyRestriction X.toRingedSpace p
    (homOfLE (inf_le_left : U ⊓ V ≤ U))
  let iV (p : ℕ) := openModuleCohomologyRestriction X.toRingedSpace p
    (homOfLE (inf_le_right : U ⊓ V ≤ V))
  choose ru hru using fun p => fraction_map_exists L F s p p (U ⊔ V) U (rU p)
  choose rv hrv using fun p => fraction_map_exists L F s p p (U ⊔ V) V (rV p)
  choose iu hiu using fun p => fraction_map_exists L F s p p U (U ⊓ V) (iU p)
  choose iv hiv using fun p => fraction_map_exists L F s p p V (U ⊓ V) (iV p)
  choose d hd using fun p => fraction_map_exists L F s p (p + 1) (U ⊓ V) (U ⊔ V) (δ U V p)
  let a (p : ℕ) := (ru p).prod (rv p)
  let b (p : ℕ) := (iu p).comp (AddMonoidHom.fst _ _) -
    (iv p).comp (AddMonoidHom.snd _ _)
  have ha (p n : ℕ) (ξ : (openModuleCohomology X.toRingedSpace p (U ⊔ V)).obj
      (F ⊗ L.tensorPow n : X.Modules)) :
      a p (cohomologyFraction L F s p (U ⊔ V) n ξ) =
        (cohomologyFraction L F s p U n ((rU p).app _ ξ),
          cohomologyFraction L F s p V n ((rV p).app _ ξ)) := by
    change (ru p _, rv p _) = _
    rw [hru, hrv]
  have hb (p n : ℕ)
      (ξ : (openModuleCohomology X.toRingedSpace p U).obj (F ⊗ L.tensorPow n : X.Modules))
      (η : (openModuleCohomology X.toRingedSpace p V).obj (F ⊗ L.tensorPow n : X.Modules)) :
      b p (cohomologyFraction L F s p U n ξ, cohomologyFraction L F s p V n η) =
        cohomologyFraction L F s p (U ⊓ V) n ((iU p).app _ ξ - (iV p).app _ η) := by
    change iu p (cohomologyFraction L F s p U n ξ) -
      iv p (cohomologyFraction L F s p V n η) = _
    rw [hiu, hiv]
    exact ((fractionOf L F s p (U ⊓ V) n).map_sub _ _).symm
  refine ⟨a, b, d, ha, ?_, ?_, hd, ?_, ?_⟩
  · intro p n ξ
    have h := hb p n ξ 0
    simpa only [fraction_zero, map_zero, sub_zero] using h
  · intro p n η
    have h := hb p n 0 η
    simpa only [fraction_zero, map_zero, zero_sub, fraction_neg] using h
  · apply (injective_iff_map_eq_zero (a 0)).mpr
    intro x hx
    obtain ⟨n, ξ, rfl⟩ := fraction_exists L F s 0 (U ⊔ V) x
    rw [ha] at hx
    obtain ⟨k, ζ, hζ, hU, hV⟩ := fraction_kill_pair L F s 0 0 0 (U ⊔ V) U V
      (rU 0) (rV 0) n ξ (congrArg Prod.fst hx) (congrArg Prod.snd hx)
    have hz : ζ = 0 := _hinj U V (F ⊗ L.tensorPow k : X.Modules)
      (show ((rU 0).app _ ζ, (rV 0).app _ ζ) =
        ((rU 0).app _ 0, (rV 0).app _ 0) by rw [hU, hV, map_zero, map_zero])
    rw [hζ, hz]
    exact (fractionOf L F s 0 (U ⊔ V) k).map_zero
  · intro p
    refine ⟨?_, ?_, ?_⟩
    · intro x
      obtain ⟨n, ξ, η, hξ, hη⟩ := fraction_pair_exists L F s p p U V x.1 x.2
      have hx : x = (cohomologyFraction L F s p U n ξ,
          cohomologyFraction L F s p V n η) := Prod.ext hξ hη
      rw [hx, hb]
      constructor
      · intro h
        obtain ⟨c, hc⟩ := cohomologyFraction_eventually_zero L F s p (U ⊓ V) n _ h
        let ξ' := (openModuleCohomology X.toRingedSpace p U).map
          (mulTensorPowSection (homOfGlobalSection L s) F n c) ξ
        let η' := (openModuleCohomology X.toRingedSpace p V).map
          (mulTensorPowSection (homOfGlobalSection L s) F n c) η
        have hz : (iU p).app _ ξ' - (iV p).app _ η' = 0 := by
          dsimp only [ξ', η']
          rw [fraction_naturality, fraction_naturality, ← map_sub]
          exact hc
        obtain ⟨ζ, hζ⟩ := (_hexact U V (F ⊗ L.tensorPow (n + c) : X.Modules) p).1
          (ξ', η') |>.mp hz
        refine ⟨cohomologyFraction L F s p (U ⊔ V) (n + c) ζ, ?_⟩
        rw [ha, show (rU p).app _ ζ = ξ' from congrArg Prod.fst hζ,
          show (rV p).app _ ζ = η' from congrArg Prod.snd hζ]
        exact Prod.ext (fraction_transition L F s p U n c ξ).symm
          (fraction_transition L F s p V n c η).symm
      · rintro ⟨y, hy⟩
        obtain ⟨k, ζ, rfl⟩ := fraction_exists L F s p (U ⊔ V) y
        have hzero := (_hexact U V (F ⊗ L.tensorPow k : X.Modules) p).1.apply_apply_eq_zero ζ
        have hcomp : b p (a p (cohomologyFraction L F s p (U ⊔ V) k ζ)) = 0 := by
          rw [ha, hb, hzero]
          exact (fractionOf L F s p (U ⊓ V) k).map_zero
        rw [hy, hb] at hcomp
        exact hcomp
    · intro x
      obtain ⟨n, ξ, rfl⟩ := fraction_exists L F s p (U ⊓ V) x
      rw [hd]
      constructor
      · intro h
        obtain ⟨c, hc⟩ := cohomologyFraction_eventually_zero L F s (p + 1) (U ⊔ V) n _ h
        let ξ' := (openModuleCohomology X.toRingedSpace p (U ⊓ V)).map
          (mulTensorPowSection (homOfGlobalSection L s) F n c) ξ
        have hz : (δ U V p).app _ ξ' = 0 := by
          dsimp only [ξ']
          rw [fraction_naturality]
          exact hc
        obtain ⟨ζ, hζ⟩ := (_hexact U V (F ⊗ L.tensorPow (n + c) : X.Modules) p).2.1 ξ'
          |>.mp hz
        refine ⟨(cohomologyFraction L F s p U (n + c) ζ.1,
          cohomologyFraction L F s p V (n + c) ζ.2), ?_⟩
        change (iU p).app _ ζ.1 - (iV p).app _ ζ.2 = ξ' at hζ
        rw [hb, hζ]
        exact (fraction_transition L F s p (U ⊓ V) n c ξ).symm
      · rintro ⟨y, hy⟩
        obtain ⟨k, ζ, η, hζ, hη⟩ := fraction_pair_exists L F s p p U V y.1 y.2
        have hzero := (_hexact U V (F ⊗ L.tensorPow k : X.Modules) p).2.1
          |>.apply_apply_eq_zero (ζ, η)
        have hcomp : d p (b p (cohomologyFraction L F s p U k ζ,
            cohomologyFraction L F s p V k η)) = 0 := by
          rw [hb, hd, hzero]
          exact (fractionOf L F s (p + 1) (U ⊔ V) k).map_zero
        have hy' : b p (cohomologyFraction L F s p U k ζ,
            cohomologyFraction L F s p V k η) =
            cohomologyFraction L F s p (U ⊓ V) n ξ := by
          rw [← hζ, ← hη]
          exact hy
        rw [hy', hd] at hcomp
        exact hcomp
    · intro x
      obtain ⟨n, ξ, rfl⟩ := fraction_exists L F s (p + 1) (U ⊔ V) x
      rw [ha]
      constructor
      · intro h
        obtain ⟨k, ζ, hζ, hU, hV⟩ := fraction_kill_pair L F s (p + 1) (p + 1) (p + 1)
          (U ⊔ V) U V (rU (p + 1)) (rV (p + 1)) n ξ
          (congrArg Prod.fst h) (congrArg Prod.snd h)
        obtain ⟨η, hη⟩ := (_hexact U V (F ⊗ L.tensorPow k : X.Modules) p).2.2 ζ
          |>.mp (show ((rU (p + 1)).app _ ζ, (rV (p + 1)).app _ ζ) = 0 by
            rw [hU, hV]; rfl)
        refine ⟨cohomologyFraction L F s p (U ⊓ V) k η, ?_⟩
        rw [hd, hη]
        exact hζ.symm
      · rintro ⟨y, hy⟩
        obtain ⟨k, ζ, rfl⟩ := fraction_exists L F s p (U ⊓ V) y
        have hzero := (_hexact U V (F ⊗ L.tensorPow k : X.Modules) p).2.2.apply_apply_eq_zero ζ
        have hcomp : a (p + 1) (d p (cohomologyFraction L F s p (U ⊓ V) k ζ)) = 0 := by
          rw [hd, ha, show (rU (p + 1)).app _ ((δ U V p).app _ ζ) = 0
            from congrArg Prod.fst hzero,
            show (rV (p + 1)).app _ ((δ U V p).app _ ζ) = 0 from congrArg Prod.snd hzero]
          simp only [fraction_zero]
          rfl
        rw [hy, ha] at hcomp
        exact hcomp

end AlgebraicGeometry
