/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Homogeneous lifting in an away localization

Source: Stacks Project, Algebra, Section 00JM; Constructions, Lemma 01M7.
(blueprint: lem-sc-p1-away-degreezero-lift)
-/

@[expose] public section

universe u v w

open MvPolynomial

namespace LocalizedModule

private theorem shift_component
    {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
    (𝓜 : ℤ → AddSubgroup M) (𝓝 : ℤ → AddSubgroup N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (H : M →+ N) (t : ℤ)
    (hH : ∀ z y, y ∈ 𝓜 z → H y ∈ 𝓝 (z + t)) (z : ℤ) (a : M) :
    (DirectSum.decompose 𝓝 (H a) (z + t) : N) =
      H (DirectSum.decompose 𝓜 a z : M) := by
  classical
  let P : M →+ M := (𝓜 z).subtype.comp
    ((DFinsupp.evalAddMonoidHom z).comp (DirectSum.decomposeAddEquiv 𝓜).toAddMonoidHom)
  let Q : N →+ N := (𝓝 (z + t)).subtype.comp
    ((DFinsupp.evalAddMonoidHom (z + t)).comp
      (DirectSum.decomposeAddEquiv 𝓝).toAddMonoidHom)
  have he : (Q.comp H).comp (DirectSum.coeAddMonoidHom 𝓜) =
      (H.comp P).comp (DirectSum.coeAddMonoidHom 𝓜) := by
    apply DirectSum.addHom_ext
    intro i y
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of]
    change (DirectSum.decompose 𝓝 (H y) (z + t) : N) =
      H (DirectSum.decompose 𝓜 (y : M) z : M)
    by_cases hi : i = z
    · subst i
      rw [DirectSum.decompose_of_mem_same 𝓝 (hH z y y.property),
        DirectSum.decompose_of_mem_same 𝓜 y.property]
    · have hit : i + t ≠ z + t := by omega
      rw [DirectSum.decompose_of_mem_ne 𝓝 (hH i y y.property) hit,
        DirectSum.decompose_of_mem_ne 𝓜 y.property hi, map_zero]
  have hc : DirectSum.coeAddMonoidHom 𝓜 (DirectSum.decompose 𝓜 a) = a :=
    (DirectSum.decompose 𝓜).symm_apply_apply a
  have hh := DFunLike.congr_fun he (DirectSum.decompose 𝓜 a)
  change Q (H a) = H (P a)
  simpa only [AddMonoidHom.comp_apply, hc] using hh

/-- A degree-zero fraction in the image of a graded localized map has a degree-zero preimage.
Source: Stacks Project, Algebra, Section 00JM, homogeneous localization; Constructions,
Lemma 01M7, final functoriality paragraph.
(blueprint: lem-sc-p1-away-degreezero-lift)

Proof: If f = 0, localization is the zero module and its zero fraction is a preimage.
Otherwise a power f^m is nonzero and has degree m*d. The total degree of this nonzero
polynomial makes every equal-degree fraction have numerator of degree m*d. Write an arbitrary
preimage as a/f^r. Equality of fractions gives a power f^l such that
f^(l+m) g(a) = f^(l+r) b. The additive map H(a) = f^(l+m) g(a) shifts each homogeneous
degree by (l+m)*d. Projections onto components commute with this degree shift: prove the
identity on each generator of the source direct sum, using independence in the target, then
extend it additively. Apply it in degree r*d. The right side f^(l+r) b has degree
(l+r)*d+m*d = r*d+(l+m)*d, so its projection is itself. Thus H(a_(r*d)) = f^(l+r) b.
The same fraction equality criterion shows a_(r*d)/f^r maps to b/f^m, and it is an
equal-degree fraction. Zero numerators and zero images cause no exception: zero belongs to
every homogeneous component. No compatibility of scalar multiplication in the source grading
is needed, and the argument also works when d=0. -/
theorem away_degreeZero_lift
    (k : Type u) [Field k]
    (M : Type v) (N : Type w) [AddCommGroup M] [AddCommGroup N]
    [Module (MvPolynomial (Fin 2) k) M] [Module (MvPolynomial (Fin 2) k) N]
    (𝓜 : ℤ → AddSubgroup M) (𝓝 : ℤ → AddSubgroup N)
    (h𝓜 : DirectSum.IsInternal 𝓜) (h𝓝 : DirectSum.IsInternal 𝓝)
    (hsmulN : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : N),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓝 z → a • y ∈ 𝓝 (n + z))
    (f : MvPolynomial (Fin 2) k) (d : ℕ)
    (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
    (g : M →ₗ[MvPolynomial (Fin 2) k] N)
    (hg : ∀ (z : ℤ) (y : M), y ∈ 𝓜 z → g y ∈ 𝓝 z)
    (x : LocalizedModule.Away f N)
    (hx : x ∈ degreeZeroFractions
      (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
      (fun n : ℕ ↦ (𝓝 n : Set N)) (Submonoid.powers f))
    (himage : x ∈ Set.range (IsLocalizedModule.map (Submonoid.powers f)
      (mkLinearMap (Submonoid.powers f) M) (mkLinearMap (Submonoid.powers f) N) g)) :
    ∃ y ∈ degreeZeroFractions
      (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
      (fun n : ℕ ↦ (𝓜 n : Set M)) (Submonoid.powers f),
      IsLocalizedModule.map (Submonoid.powers f)
        (mkLinearMap (Submonoid.powers f) M) (mkLinearMap (Submonoid.powers f) N) g y = x := by
  classical
  let := h𝓜.chooseDecomposition
  let := h𝓝.chooseDecomposition
  have hp (r : ℕ) : f ^ r ∈ homogeneousSubmodule (Fin 2) k (d * r) :=
    (show f.IsHomogeneous d from hf).pow r
  by_cases hzero : f = 0
  · have hT : (0 : MvPolynomial (Fin 2) k) ∈ Submonoid.powers f :=
      ⟨1, by simp [hzero]⟩
    have : Subsingleton (LocalizedModule.Away f N) := subsingleton hT
    refine ⟨0, ?_, Subsingleton.elim _ _⟩
    exact ⟨0, 0, 1, (𝓜 0).zero_mem, isHomogeneous_one (Fin 2) k, zero_mk 1⟩
  · obtain ⟨n, b, s, hb, hs, hbx⟩ := hx
    obtain ⟨y, hy⟩ := himage
    obtain ⟨a, t, hat⟩ := (show ∀ y : LocalizedModule.Away f M, ∃ a t, mk a t = y from
      fun y ↦ induction_on (fun a t ↦ ⟨a, t, rfl⟩) y) y
    obtain ⟨r, hr⟩ := t.property
    have ht : t = (⟨f ^ r, ⟨r, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext hr.symm
    subst t
    obtain ⟨m, hm⟩ := s.property
    have ht : s = (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext hm.symm
    subst s
    have hn : n = d * m :=
      (show (f ^ m).IsHomogeneous n from hs).totalDegree (pow_ne_zero m hzero) |>.symm.trans
        ((show (f ^ m).IsHomogeneous (d * m) from hp m).totalDegree (pow_ne_zero m hzero))
    subst n
    have heq : mk (g a) (⟨f ^ r, ⟨r, rfl⟩⟩ : Submonoid.powers f) =
        mk b (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := by
      rw [← IsLocalizedModule.map_LocalizedModules, hat]
      exact hy.trans hbx.symm
    obtain ⟨u, hu⟩ := mk_eq.mp heq
    obtain ⟨l, hl⟩ := u.property
    have hut : u = (⟨f ^ l, ⟨l, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext hl.symm
    subst u
    have hu' : f ^ (l + m) • g a = f ^ (l + r) • b := by
      simpa only [Submonoid.smul_def, ← mul_smul, ← pow_add] using hu
    let H : M →+ N :=
      { toFun := fun a ↦ f ^ (l + m) • g a
        map_zero' := by simp
        map_add' := by intros; simp [smul_add] }
    have hH (z : ℤ) (a : M) (ha : a ∈ 𝓜 z) :
        H a ∈ 𝓝 (z + (d * (l + m) : ℕ)) := by
      change f ^ (l + m) • g a ∈ _
      simpa only [add_comm] using hsmulN (d * (l + m)) z _ _ (hp (l + m)) (hg z a ha)
    have hb' : f ^ (l + r) • b ∈ 𝓝 ((d * r : ℕ) + (d * (l + m) : ℕ)) := by
      have hedeg : ((d * (l + r) : ℕ) : ℤ) + (d * m : ℕ) =
          (d * r : ℕ) + (d * (l + m) : ℕ) := by push_cast; ring
      rw [← hedeg]
      exact hsmulN (d * (l + r)) (d * m) _ _ (hp (l + r)) hb
    let a₀ := (DirectSum.decompose 𝓜 a (d * r : ℕ) : M)
    have ha₀ : a₀ ∈ 𝓜 (d * r : ℕ) :=
      (DirectSum.decompose 𝓜 a (d * r : ℕ)).property
    have hc : H a₀ = f ^ (l + r) • b := by
      rw [← shift_component 𝓜 𝓝 H (d * (l + m) : ℕ) hH (d * r : ℕ) a]
      change (DirectSum.decompose 𝓝 (f ^ (l + m) • g a) _ : N) = _
      rw [hu', DirectSum.decompose_of_mem_same 𝓝 hb']
    refine ⟨mk a₀ (⟨f ^ r, ⟨r, rfl⟩⟩ : Submonoid.powers f), ?_, ?_⟩
    · exact ⟨d * r, a₀, _, ha₀, hp r, rfl⟩
    · rw [IsLocalizedModule.map_LocalizedModules, ← hbx]
      apply mk_eq.mpr
      refine ⟨⟨f ^ l, ⟨l, rfl⟩⟩, ?_⟩
      change f ^ (l + m) • g a₀ = f ^ (l + r) • b at hc
      simpa only [Submonoid.smul_def, ← mul_smul, ← pow_add] using hc

end LocalizedModule
