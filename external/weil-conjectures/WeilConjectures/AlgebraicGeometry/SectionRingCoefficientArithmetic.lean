/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

private theorem restrict_mul {X : Scheme.{v}} (L : X.Modules) [L.IsInvertible]
    (U : X.Opens) {i j : ℕ} (a : sectionRingGrade L i) (b : sectionRingGrade L j) :
    (L.tensorPow (i + j)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      ((a.val * b.val) (i + j)) =
    (L.tensorPowAddIso i j).inv.app U
      (tmulSection
        ((L.tensorPow i).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (a.val i))
        ((L.tensorPow j).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (b.val j))) := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  simp only [DirectSum.of_mul_of, DirectSum.of_eq_same]
  change (L.tensorPow (i + j)).presheaf.map _
    ((L.tensorPowAddIso i j).inv.app ⊤ (tmulSection a b)) = _
  rw [← Hom.app_presheaf_map, tmulSection_map]

/-- The numerator equation uniquely determines the coefficient function and its ring laws.
This is the uniqueness and arithmetic part of the quotient construction (Stacks Tags 01N8, 01NK).
(blueprint: lem-sc-section-ring-coefficient-data-arithmetic)

As in the numerator construction, restriction of s^n is a free generator e_n:
induct using the unit generator, hs, tensor products and tensorPowAddIso.
Apply hn to the degree-zero numerators zero and one, both with denominator s^0.
Scalar multiplication by e_0 is injective, so c(0)=0 and c(1)=1.
For arbitrary fractions use Away.mk_surjective to write a/s^n and b/s^m.
Their sum has numerator a*s^m+b*s^n and denominator s^(n+m).
Restrict this identity and apply hn to both summands. Bilinearity gives
(c(a/s^n)+c(b/s^m)) • e_(n+m) as its numerator section; hn for the sum
and injectivity for e_(n+m) prove additivity. The product has numerator a*b
and the same denominator s^(n+m). Tensor bilinearity gives
(c(a/s^n)*c(b/s^m)) • e_(n+m); the same injectivity proves multiplicativity.
All degree transports are the tensorPowAddIso transports in sectionRingGMul,
and restriction commutes with them by naturality. No cancellation in the
global section ring is assumed. -/
theorem sectionRing_coefficient_arithmetic_of_numerator
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (hd : 0 < d) (U : X.Opens)
    (hs : IsFreeGenerator ((L.tensorPow d).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (s.val d)))
    (c : HomogeneousLocalization.Away (sectionRingGrade L) s.val → Γ(X, U))
    (hn : ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
      c (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
          ξ.val ξ.property) •
        (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          ((s.val ^ n) (n • d)) =
      (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (ξ.val (n • d))) :
    c 0 = 0 ∧ c 1 = 1 ∧ (∀ a b, c (a + b) = c a + c b) ∧
      (∀ a b, c (a * b) = c a * c b) := by
  have _ := hd
  let r (k : ℕ) (a : InvertibleSectionRing L) : Γ(L.tensorPow k, U) :=
    (L.tensorPow k).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (a k)
  have hg (n : ℕ) : IsFreeGenerator (r (n • d) (s.val ^ n)) := by
    induction n with
    | zero =>
      dsimp only [r]
      rw [zero_nsmul, pow_zero, DirectSum.one_def, DirectSum.of_eq_same]
      change IsFreeGenerator ((L.tensorPow 0).presheaf.map
        (homOfLE (le_top : U ≤ ⊤)).op (unitSectionsEquiv ⊤ 1))
      intro V hV
      rw [presheaf_map_map_apply]
      erw [presheaf_map_unitSectionsEquiv, map_one]
      have hf : (fun a : Γ(X, V) ↦ a • unitSectionsEquiv (X := X) V 1) =
          unitSectionsEquiv (X := X) V := by
        funext a
        exact (unitSectionsEquiv_eq_smul_one a).symm
      rw [hf]
      exact (unitSectionsEquiv V).bijective
    | succ n ih =>
      dsimp only [r] at ih ⊢
      rw [succ_nsmul, pow_succ]
      rw [restrict_mul L U
        ⟨s.val ^ n, SetLike.pow_mem_graded n s.property⟩ s]
      exact (ih.tmulSection hs).app_hom (L.tensorPowAddIso (n • d) d).symm
  have hmul {i j : ℕ} (a e : sectionRingGrade L i) (b f : sectionRingGrade L j)
      (x y : Γ(X, U)) (ha : r i a.val = x • r i e.val)
      (hb : r j b.val = y • r j f.val) :
      r (i + j) (a.val * b.val) = (x * y) • r (i + j) (e.val * f.val) := by
    dsimp only [r] at ha hb ⊢
    rw [restrict_mul L U a b, restrict_mul L U e f, ha, hb,
      smul_tmulSection, tmulSection_smul, Hom.app_smul, Hom.app_smul, smul_smul]
  have hz : HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property 0
      0 (zero_mem _) = 0 := by
    apply HomogeneousLocalization.val_injective
    simp [Localization.mk_zero]
  have ho : HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property 0
      1 (by simpa using (SetLike.pow_mem_graded 0 s.property)) = 1 := by
    apply HomogeneousLocalization.val_injective
    simp
  have h0 : c 0 = 0 := by
    apply (hg 0).smul_left_injective
    have h := hn 0 ⟨0, zero_mem _⟩
    simpa only [hz, DFinsupp.zero_apply, map_zero, zero_smul] using h
  have h1 : c 1 = 1 := by
    apply (hg 0).smul_left_injective
    have h := hn 0 ⟨1, by simpa using (SetLike.pow_mem_graded 0 s.property)⟩
    simpa only [ho, pow_zero, one_smul] using h
  refine ⟨h0, h1, ?_, ?_⟩
  · intro a b
    obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (sectionRingGrade L) s.property a
    obtain ⟨m, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (sectionRingGrade L) s.property b
    let an : sectionRingGrade L (n • d) := ⟨a, ha⟩
    let bm : sectionRingGrade L (m • d) := ⟨b, hb⟩
    let sn : sectionRingGrade L (n • d) := ⟨s.val ^ n, SetLike.pow_mem_graded n s.property⟩
    let sm : sectionRingGrade L (m • d) := ⟨s.val ^ m, SetLike.pow_mem_graded m s.property⟩
    let qa := HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n a ha
    let qb := HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property m b hb
    have hnum : a * s.val ^ m + s.val ^ n * b ∈ sectionRingGrade L ((n + m) • d) := by
      rw [add_nsmul]
      exact add_mem (SetLike.mul_mem_graded ha sm.property)
        (SetLike.mul_mem_graded sn.property hb)
    let z : sectionRingGrade L ((n + m) • d) := ⟨_, hnum⟩
    have hq : HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property
        (n + m) z.val z.property = qa + qb := by
      apply HomogeneousLocalization.val_injective
      simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_add,
        qa, qb, z]
      rw [Localization.add_mk]
      congr 1
      · rw [mul_comm a, add_comm]
      · apply Subtype.ext
        exact pow_add _ _ _
    apply (hg (n + m)).smul_left_injective
    have h := hn (n + m) z
    rw [hq] at h
    change c (qa + qb) • r ((n + m) • d) (s.val ^ (n + m)) = _ at h
    change c (qa + qb) • r ((n + m) • d) (s.val ^ (n + m)) =
      (c qa + c qb) • r ((n + m) • d) (s.val ^ (n + m))
    rw [h]
    rw [add_smul (c qa) (c qb)]
    have ha' := hmul an sn sm sm (c qa) 1 (hn n an).symm (one_smul _ _).symm
    have hb' := hmul sn sn bm sm 1 (c qb) (one_smul _ _).symm (hn m bm).symm
    dsimp only [an, bm, sn, sm] at ha' hb'
    simp only [mul_one, one_mul] at ha' hb'
    rw [← add_nsmul, ← pow_add] at ha' hb'
    change r ((n + m) • d) (a * s.val ^ m + s.val ^ n * b) = _
    rw [← ha', ← hb']
    dsimp only [r, an, bm, sn, sm]
    rw [DFinsupp.add_apply, map_add]
  · intro a b
    obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (sectionRingGrade L) s.property a
    obtain ⟨m, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (sectionRingGrade L) s.property b
    let an : sectionRingGrade L (n • d) := ⟨a, ha⟩
    let bm : sectionRingGrade L (m • d) := ⟨b, hb⟩
    let sn : sectionRingGrade L (n • d) := ⟨s.val ^ n, SetLike.pow_mem_graded n s.property⟩
    let sm : sectionRingGrade L (m • d) := ⟨s.val ^ m, SetLike.pow_mem_graded m s.property⟩
    let qa := HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n a ha
    let qb := HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property m b hb
    have hnum : a * b ∈ sectionRingGrade L ((n + m) • d) := by
      rw [add_nsmul]
      exact SetLike.mul_mem_graded ha hb
    let z : sectionRingGrade L ((n + m) • d) := ⟨a * b, hnum⟩
    have hq : HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property
        (n + m) z.val z.property = qa * qb := by
      apply HomogeneousLocalization.val_injective
      simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_mul,
        qa, qb, z]
      rw [Localization.mk_mul]
      congr 1
      apply Subtype.ext
      exact pow_add _ _ _
    apply (hg (n + m)).smul_left_injective
    have h := hn (n + m) z
    rw [hq] at h
    change c (qa * qb) • r ((n + m) • d) (s.val ^ (n + m)) = _ at h
    change c (qa * qb) • r ((n + m) • d) (s.val ^ (n + m)) =
      (c qa * c qb) • r ((n + m) • d) (s.val ^ (n + m))
    rw [h]
    have hab := hmul an sn bm sm (c qa) (c qb) (hn n an).symm (hn m bm).symm
    dsimp only [an, bm, sn, sm] at hab
    rw [← add_nsmul, ← pow_add] at hab
    exact hab
end AlgebraicGeometry.Scheme.Modules
