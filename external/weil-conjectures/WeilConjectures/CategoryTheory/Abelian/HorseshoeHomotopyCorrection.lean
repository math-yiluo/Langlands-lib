/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDefectFactorization
import Mathlib.Tactic.Abel

/-!
# Correction of horseshoe comparison defects

Source: the classical horseshoe naturality argument of Weibel, Theorem 2.4.6,
using Stacks Project, Tags 0136, 013R, 013P and 013T
(blueprint: lem-weil-pbc-horseshoe-homotopy-correction).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveResolution

private theorem signed_primitive
    {C : Type u} [Category.{v} C] [Abelian C] {U V : C}
    (I : InjectiveResolution U) (J : InjectiveResolution V)
    (e : U ⟶ J.cocomplex.X 0)
    (E : ∀ n, I.cocomplex.X n ⟶ J.cocomplex.X (n + 1))
    (he : I.ι.f 0 ≫ E 0 = e ≫ J.cocomplex.d 0 1)
    (hE : ∀ n, I.cocomplex.d n (n + 1) ≫ E (n + 1) =
      -(E n ≫ J.cocomplex.d (n + 1) (n + 2))) :
    ∃ k : ∀ n, I.cocomplex.X n ⟶ J.cocomplex.X n,
      I.ι.f 0 ≫ k 0 = e ∧
      ∀ n, I.cocomplex.d n (n + 1) ≫ k (n + 1) =
        k n ≫ J.cocomplex.d n (n + 1) - E n := by
  classical
  let k₀ : I.cocomplex.X 0 ⟶ J.cocomplex.X 0 :=
    Injective.factorThru e (I.ι.f 0)
  have hk₀ : I.ι.f 0 ≫ k₀ = e := Injective.comp_factorThru _ _
  have hzero : I.ι.f 0 ≫ (k₀ ≫ J.cocomplex.d 0 1 - E 0) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, hk₀, he, sub_self]
  let k₁ : I.cocomplex.X 1 ⟶ J.cocomplex.X 1 :=
    I.exact₀.descToInjective (k₀ ≫ J.cocomplex.d 0 1 - E 0) hzero
  have hk₁ : I.cocomplex.d 0 1 ≫ k₁ = k₀ ≫ J.cocomplex.d 0 1 - E 0 :=
    I.exact₀.comp_descToInjective _ _
  have step (n : ℕ)
      (a : I.cocomplex.X n ⟶ J.cocomplex.X n)
      (b : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X (n + 1))
      (hab : I.cocomplex.d n (n + 1) ≫ b =
        a ≫ J.cocomplex.d n (n + 1) - E n) :
      ∃ c : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 2),
        I.cocomplex.d (n + 1) (n + 2) ≫ c =
          b ≫ J.cocomplex.d (n + 1) (n + 2) - E (n + 1) := by
    have hz : I.cocomplex.d n (n + 1) ≫
        (b ≫ J.cocomplex.d (n + 1) (n + 2) - E (n + 1)) = 0 := by
      rw [Preadditive.comp_sub, ← Category.assoc, hab, Preadditive.sub_comp,
        Category.assoc, HomologicalComplex.d_comp_d, comp_zero, zero_sub, hE,
        sub_self]
    exact ⟨(I.exact_succ n).descToInjective _ hz,
      (I.exact_succ n).comp_descToInjective _ hz⟩
  choose next hnext using step
  let pairs : ∀ n, Σ' (a : I.cocomplex.X n ⟶ J.cocomplex.X n)
      (b : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X (n + 1)),
      I.cocomplex.d n (n + 1) ≫ b = a ≫ J.cocomplex.d n (n + 1) - E n :=
    fun n ↦ Nat.rec ⟨k₀, k₁, hk₁⟩ (fun n p ↦
      ⟨p.2.1, next n p.1 p.2.1 p.2.2, hnext n p.1 p.2.1 p.2.2⟩) n
  refine ⟨fun n ↦ (pairs n).1, hk₀, ?_⟩
  intro n
  exact (pairs n).2.2

set_option backward.isDefEq.respectTransparency false in
/-- Correct the differential and augmentation defects of a prescribed degreewise map.
Factor the defects as in `horseshoe_defect_factorization`, obtaining E and e. Extend e
across the monic augmentation of IC into the injective degree-zero term of JA, giving k₀.
The relation ιC E₀ = e dA' makes k₀ dA' - E₀ descend along dC₀, giving k₁.
Inductively, if dCₙ kₙ₊₁ = kₙ dA'ₙ - Eₙ, the signed cocycle identity and d² = 0
show that kₙ₊₁ dA'ₙ₊₁ - Eₙ₊₁ vanishes on dCₙ. Exactness of IC and injectivity of
JA let it descend along dCₙ₊₁, defining kₙ₊₂. This is the inductive null-homotopy
argument of Tag 013R specialized to the augmented resolution, with its signs undone.
The resulting identities cancel both defects of t - βkα'.
Source: Stacks Project, derived.tex, Tag 013R, proof by successive injective extensions;
classical horseshoe naturality Steps 2--3.
(blueprint: lem-weil-pbc-horseshoe-homotopy-correction) -/
theorem horseshoe_homotopy_correction
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : ShortComplex C) (hS : S.ShortExact) (hT : T.ShortExact) (F : S ⟶ T)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃) (JA : InjectiveResolution T.X₁)
    (JB : InjectiveResolution T.X₂) (JC : InjectiveResolution T.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (α' : JA.cocomplex ⟶ JB.cocomplex) (β' : JB.cocomplex ⟶ JC.cocomplex)
    (hαβ : α ≫ β = 0) (hαβ' : α' ≫ β' = 0)
    (hα : IA.ι ≫ α = (CochainComplex.single₀ C).map S.f ≫ IB.ι)
    (hβ : IB.ι ≫ β = (CochainComplex.single₀ C).map S.g ≫ IC.ι)
    (hα' : JA.ι ≫ α' = (CochainComplex.single₀ C).map T.f ≫ JB.ι)
    (hβ' : JB.ι ≫ β' = (CochainComplex.single₀ C).map T.g ≫ JC.ι)
    (hexact : ∀ n : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (hexact' : ∀ n : ℕ, ((ShortComplex.mk α' β' hαβ').map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (φA : IA.cocomplex ⟶ JA.cocomplex) (φC : IC.cocomplex ⟶ JC.cocomplex)
    (hφA : IA.ι ≫ φA = (CochainComplex.single₀ C).map F.τ₁ ≫ JA.ι)
    (hφC : IC.ι ≫ φC = (CochainComplex.single₀ C).map F.τ₃ ≫ JC.ι)
    (t : ∀ n, IB.cocomplex.X n ⟶ JB.cocomplex.X n)
    (htα : ∀ n, α.f n ≫ t n = φA.f n ≫ α'.f n)
    (htβ : ∀ n, t n ≫ β'.f n = β.f n ≫ φC.f n) :
    ∃ k : ∀ n, IC.cocomplex.X n ⟶ JA.cocomplex.X n,
      (∀ n,
        (t n - β.f n ≫ k n ≫ α'.f n) ≫ JB.cocomplex.d n (n + 1) =
          IB.cocomplex.d n (n + 1) ≫
            (t (n + 1) - β.f (n + 1) ≫ k (n + 1) ≫ α'.f (n + 1))) ∧
      IB.ι.f 0 ≫ (t 0 - β.f 0 ≫ k 0 ≫ α'.f 0) =
        ((CochainComplex.single₀ C).map F.τ₂ ≫ JB.ι).f 0 := by
  obtain ⟨E, e, hD, hw, he, hE⟩ := horseshoe_defect_factorization
    S T hS hT F IA IB IC JA JB JC α β α' β' hαβ hαβ' hα hβ hα' hβ'
    hexact hexact' φA φC hφA hφC t htα htβ
  obtain ⟨k, hk₀, hk⟩ := signed_primitive IC JA e E he hE
  refine ⟨k, ?_, ?_⟩
  · intro n
    have hk' : k n ≫ JA.cocomplex.d n (n + 1) =
        IC.cocomplex.d n (n + 1) ≫ k (n + 1) + E n := by
      exact (eq_sub_iff_add_eq.mp (hk n)).symm
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, α'.comm,
      ← Category.assoc (k n), hk', Preadditive.add_comp, Preadditive.comp_add,
      Preadditive.comp_sub]
    simp only [Category.assoc]
    rw [reassoc_of% (β.comm n (n + 1))]
    have hd := hD n
    rw [eq_sub_iff_add_eq] at hd
    rw [← hd]
    abel
  · have hb : IB.ι.f 0 ≫ β.f 0 = S.g ≫ IC.ι.f 0 := by
      simpa using HomologicalComplex.congr_hom hβ 0
    rw [Preadditive.comp_sub, ← Category.assoc, ← Category.assoc, hb,
      Category.assoc (S.g)]
    simp only [Category.assoc, reassoc_of% hk₀]
    rw [hw, sub_sub_cancel]

end CategoryTheory.InjectiveResolution
