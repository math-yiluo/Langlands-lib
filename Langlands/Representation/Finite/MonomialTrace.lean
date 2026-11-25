/-
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Adapted from the Anthropic Lean formalization of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, files
`Theorems/Thm_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.lean`
and
`P2M/Sol/S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.lean`
(all but its sections `Rep` and `Trace`, which are in `WeightSpaces`).
Changes: statement and proof in one file; declarations moved into
`Langlands.FiniteRep.MonomialTrace`, the end theorem renamed; groups and carriers may lie in any
universes; Mathlib is imported by module and no option is set; unused instance arguments are
omitted; linter clean-ups. The paired Markdown file lists the changes.
-/
import Langlands.Representation.Finite.ClassFunctionInduction
import Langlands.Representation.Finite.WeightSpaces
import Mathlib.Algebra.DirectSum.LinearMap

/-!
# The monomial case of Brauer's theorem

`exists_trace_eq_sum_inducedClassFunction_linearCharacter`: let `G` be a finite group, `p` a
prime and `A` a normal commutative subgroup such that every element of `G` has a `p`-power in `A`.
Then the trace of every complex matrix representation `ρ : G →* GL (Fin n) ℂ` is a finite sum of
class functions `inducedClassFunction H (extension by zero of ψ)` induced from linear characters
`ψ : H →* ℂˣ` of subgroups `H` (with repetitions, no signs).

The proof is an induction on `|K| + dim W` (`engine`) over representations `σ` of groups `K` with
such a subgroup, in the bookkeeping of lists of pairs (subgroup, linear character) (`Entry`,
`lsum`). Either `σ` has commuting image, and its weight spaces for `⊤` give the trace directly;
or a normal commutative subgroup `B ≥ A` acts by non-scalars (`exists_normal_comm_not_central`),
and the weight spaces of `B` (`WeightSpaces`) are either permuted transitively by `K`, so that the
trace is induced from the stabilizer of a weight (`monomial_of_transitive`), or split into two
nonzero `K`-stable pieces (`monomial_of_isCompl`).
-/

noncomputable section

open scoped Classical
open Module
open Langlands.FiniteRep.WeightSpaces

namespace Langlands.FiniteRep.MonomialTrace

universe u v

section Bookkeeping

variable {K : Type u} [Group K] [Fintype K]

/-- The extension by zero of a character `ψ` of a subgroup `L` to a function on `K`. -/
def extChar (L : Subgroup K) (ψ : L →* ℂˣ) : K → ℂ :=
  fun x => if hx : x ∈ L then ((ψ ⟨x, hx⟩ : ℂˣ) : ℂ) else 0

/-- A subgroup with a linear character on it. -/
abbrev Entry (K : Type u) [Group K] := Σ L : Subgroup K, (L →* ℂˣ)

private def val (e : Entry K) : K → ℂ := inducedClassFunction e.1 (extChar e.1 e.2)

/-- The sum, over a list of entries, of the class functions induced from their characters. -/
def lsum (l : List (Entry K)) : K → ℂ := fun g => (l.map fun e => val e g).sum

theorem lsum_nil : lsum ([] : List (Entry K)) = 0 := by
  funext g; simp [lsum]

theorem lsum_cons (e : Entry K) (l : List (Entry K)) : lsum (e :: l) = val e + lsum l := by
  funext g; simp [lsum]

theorem lsum_append (l₁ l₂ : List (Entry K)) : lsum (l₁ ++ l₂) = lsum l₁ + lsum l₂ := by
  funext g; simp [lsum, List.sum_append]

theorem lsum_replicate (n : ℕ) (e : Entry K) (g : K) :
    lsum (List.replicate n e) g = (n : ℂ) * val e g := by
  induction n with
  | zero => simp [lsum]
  | succ n ih =>
    rw [List.replicate_succ, lsum_cons, Pi.add_apply, ih]
    push_cast
    ring

theorem lsum_flatten_replicate {X : Type*} (L : List X) (n : X → ℕ) (e : X → Entry K) (g : K) :
    lsum ((L.map fun x => List.replicate (n x) (e x)).flatten) g =
      (L.map fun x => (n x : ℂ) * val (e x) g).sum := by
  induction L with
  | nil => simp [lsum]
  | cons x L ih =>
    rw [List.map_cons, List.flatten_cons, lsum_append, Pi.add_apply, ih, lsum_replicate,
      List.map_cons, List.sum_cons]

/-- An entry of a subgroup `H`, as an entry of `K` (the image subgroup, with the transported
character). -/
def lift (H : Subgroup K) (e : Entry H) : Entry K :=
  ⟨e.1.map H.subtype,
    e.2.comp (e.1.equivMapOfInjective H.subtype H.subtype_injective).symm.toMonoidHom⟩

omit [Fintype K] in
theorem lift_snd_apply (H : Subgroup K) (e : Entry H) (x : (lift H e).1) :
    (lift H e).2 x = e.2 ((e.1.equivMapOfInjective H.subtype H.subtype_injective).symm x) := rfl

omit [Fintype K] in
theorem extChar_lift (H : Subgroup K) (e : Entry H) (g : K) (hg : g ∈ e.1.map H.subtype) :
    extChar (lift H e).1 (lift H e).2 g = if hg' : g ∈ H then extChar e.1 e.2 ⟨g, hg'⟩ else 0 := by
  obtain ⟨z, hz, rfl⟩ := hg
  change extChar (lift H e).1 (lift H e).2 (z : K) =
    if hg' : (z : K) ∈ H then extChar e.1 e.2 ⟨(z : K), hg'⟩ else 0
  rw [dite_eq_left z.2]
  have hz' : (⟨(z : K), z.2⟩ : H) ∈ e.1 := by simpa using hz
  have hmem : (z : K) ∈ (lift H e).1 := ⟨z, hz, rfl⟩
  simp only [extChar, dite_eq_left hz', dite_eq_left hmem, lift_snd_apply]
  congr 2
  apply (e.1.equivMapOfInjective H.subtype H.subtype_injective).injective
  dsimp only [lift] at hmem ⊢
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rfl

theorem val_lift (H : Subgroup K) (e : Entry H) :
    val (lift H e) = inducedClassFunction H (fun g => if hg : g ∈ H then val e ⟨g, hg⟩ else 0) := by
  rw [val]
  unfold val
  rw [inducedClassFunction_inducedClassFunction H e.1 (extChar e.1 e.2)]
  apply inducedClassFunction_congr
  intro g hg
  exact extChar_lift H e g hg

theorem inducedClassFunction_lsum_eq (H : Subgroup K) (l : List (Entry H)) :
    inducedClassFunction H (fun g => if hg : g ∈ H then lsum l ⟨g, hg⟩ else 0) =
      lsum (l.map (lift H)) := by
  induction l with
  | nil =>
    rw [List.map_nil, lsum_nil, lsum_nil]
    have : (fun g : K => if hg : g ∈ H then (0 : H → ℂ) ⟨g, hg⟩ else 0) = 0 := by
      funext g; split_ifs <;> rfl
    rw [this, inducedClassFunction_zero]
  | cons e l ih =>
    rw [List.map_cons, lsum_cons, lsum_cons, val_lift, ← ih, ← inducedClassFunction_add]
    apply inducedClassFunction_congr
    intro g hg
    simp only [Pi.add_apply, dite_eq_left hg]

end Bookkeeping

section GroupLemma

variable {K : Type u} [Group K] [Fintype K] {Γ : Type*} [Group Γ]

/-- If `K / A` is a `p`-group, `A` is normal with commuting image under `f`, and the image of `f` is
not commutative, then a normal subgroup `B ≥ A` with commuting image has an element whose image is
not central. -/
theorem exists_normal_comm_not_central {p : ℕ} (hp : p.Prime) (A : Subgroup K) [hAn : A.Normal]
    (hpow : ∀ k : K, ∃ n : ℕ, k ^ p ^ n ∈ A) (f : K →* Γ)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, f a * f b = f b * f a)
    (hnc : ∃ x y : K, f x * f y ≠ f y * f x) :
    ∃ B : Subgroup K, B.Normal ∧ A ≤ B ∧ (∀ a ∈ B, ∀ b ∈ B, f a * f b = f b * f a) ∧
      ∃ b ∈ B, ∃ k : K, f b * f k ≠ f k * f b := by
  by_cases hcase : ∃ a ∈ A, ∃ k : K, f a * f k ≠ f k * f a
  · obtain ⟨a, ha, k, hk⟩ := hcase
    exact ⟨A, hAn, le_rfl, hAcomm, a, ha, k, hk⟩
  · push Not at hcase

    let Z : Subgroup K :=
      { carrier := {z | ∀ k : K, f z * f k = f k * f z}
        one_mem' := by intro k; simp
        mul_mem' := fun {a b} ha hb k => by
          rw [map_mul, mul_assoc, hb k, ← mul_assoc, ha k, mul_assoc]
        inv_mem' := fun {a} ha k => by
          rw [map_inv]
          have := ha k
          calc (f a)⁻¹ * f k = (f a)⁻¹ * (f k * f a) * (f a)⁻¹ := by group
            _ = (f a)⁻¹ * (f a * f k) * (f a)⁻¹ := by rw [this]
            _ = f k * (f a)⁻¹ := by group }
    have hZmem : ∀ z, z ∈ Z ↔ ∀ k : K, f z * f k = f k * f z := fun z => Iff.rfl
    have hZn : Z.Normal := ⟨fun z hz g k => by
      rw [hZmem] at hz
      have h1 := hz (g⁻¹ * k * g)
      simp only [map_mul, map_inv] at h1 ⊢
      calc f g * f z * (f g)⁻¹ * f k = f g * (f z * ((f g)⁻¹ * f k * f g)) * (f g)⁻¹ := by group
        _ = f g * (((f g)⁻¹ * f k * f g) * f z) * (f g)⁻¹ := by rw [h1]
        _ = f k * (f g * f z * (f g)⁻¹) := by group⟩
    have hAZ : A ≤ Z := fun a ha k => hcase a ha k
    have : Fact p.Prime := ⟨hp⟩
    have hPG : IsPGroup p (K ⧸ Z) := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H k =>
        obtain ⟨n, hn⟩ := hpow k
        exact ⟨n, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hAZ hn⟩
    obtain ⟨x, y, hxy⟩ := hnc
    have hnt : Nontrivial (K ⧸ Z) := by
      refine ⟨⟨(x : K ⧸ Z), 1, ?_⟩⟩
      intro hx1
      rw [QuotientGroup.eq_one_iff, hZmem] at hx1
      exact hxy (hx1 y)
    obtain ⟨⟨zbar, hzc⟩, hz1⟩ :=
      (nontrivial_iff_exists_ne (1 : Subgroup.center (K ⧸ Z))).1 hPG.center_nontrivial
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective zbar
    have hzZ : z ∉ Z := by
      intro h
      apply hz1
      apply Subtype.ext
      change (z : K ⧸ Z) = 1
      rwa [QuotientGroup.eq_one_iff]

    have hzcomm : ∀ k : K, k * z * k⁻¹ * z⁻¹ ∈ Z := by
      intro k
      rw [Subgroup.mem_center_iff] at hzc
      have := hzc (k : K ⧸ Z)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at this

      have h2 : k * ((k * z)⁻¹ * (z * k)) * k⁻¹ ∈ Z := hZn.conj_mem _ this k
      have h3 : (k * ((k * z)⁻¹ * (z * k)) * k⁻¹)⁻¹ ∈ Z := Z.inv_mem h2
      have h4 := hZn.conj_mem _ h3 z
      have e : z * (k * ((k * z)⁻¹ * (z * k)) * k⁻¹)⁻¹ * z⁻¹ = k * z * k⁻¹ * z⁻¹ := by group
      rwa [e] at h4

    let B : Subgroup K := Subgroup.zpowers z ⊔ Z
    have hBmem : ∀ b : K, b ∈ B ↔ ∃ i : ℤ, ∃ w ∈ Z, z ^ i * w = b := by
      intro b
      have : b ∈ B ↔ b ∈ ((Subgroup.zpowers z ⊔ Z : Subgroup K) : Set K) := Iff.rfl
      rw [this, Subgroup.mul_normal, Set.mem_mul]
      constructor
      · rintro ⟨u, hu, w, hw, rfl⟩
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
        exact ⟨i, w, hw, rfl⟩
      · rintro ⟨i, w, hw, rfl⟩
        exact ⟨z ^ i, Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) i, w, hw, rfl⟩
    have hzB : z ∈ B := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
    have hZB : Z ≤ B := le_sup_right
    refine ⟨B, ?_, hAZ.trans hZB, ?_, z, hzB, ?_⟩
    ·
      refine ⟨fun b hb g => ?_⟩
      obtain ⟨i, w, hw, rfl⟩ := (hBmem b).1 hb
      have e : g * (z ^ i * w) * g⁻¹ = (g * z * g⁻¹) ^ i * (g * w * g⁻¹) := by
        rw [conj_zpow]; group
      rw [e]
      refine B.mul_mem (B.zpow_mem ?_ i) (hZB (hZn.conj_mem w hw g))
      have e2 : g * z * g⁻¹ = (g * z * g⁻¹ * z⁻¹) * z := by group
      rw [e2]
      exact B.mul_mem (hZB (hzcomm g)) hzB
    ·
      intro a ha b hb
      obtain ⟨i, w, hw, rfl⟩ := (hBmem a).1 ha
      obtain ⟨j, w', hw', rfl⟩ := (hBmem b).1 hb
      have hw1 := (hZmem w).1 hw
      have hw2 := (hZmem w').1 hw'
      simp only [map_mul, map_zpow]

      have c1 : f w * f (z ^ j) = f (z ^ j) * f w := hw1 (z ^ j)
      have c2 : f w * f w' = f w' * f w := hw1 w'
      have c3 : f w' * f (z ^ i) = f (z ^ i) * f w' := hw2 (z ^ i)
      rw [map_zpow] at c1 c3
      calc f z ^ i * f w * (f z ^ j * f w') = f z ^ i * (f w * f z ^ j) * f w' := by group
        _ = f z ^ i * (f z ^ j * f w) * f w' := by rw [c1]
        _ = f z ^ j * f z ^ i * (f w * f w') := by
            have hz2 : f z ^ i * f z ^ j = f z ^ j * f z ^ i := by
              rw [← zpow_add, ← zpow_add, add_comm]
            rw [show f z ^ i * (f z ^ j * f w) * f w' = (f z ^ i * f z ^ j) * (f w * f w') by group,
              hz2]
        _ = f z ^ j * f z ^ i * (f w' * f w) := by rw [c2]
        _ = f z ^ j * (f z ^ i * f w') * f w := by group
        _ = f z ^ j * (f w' * f z ^ i) * f w := by rw [c3]
        _ = f z ^ j * f w' * (f z ^ i * f w) := by group
    ·
      by_contra hall
      push Not at hall
      exact hzZ ((hZmem z).2 hall)

end GroupLemma

section Induction

/-- The trace of `σ` is `lsum l` for some list `l` of entries. -/
def Monomial (K : Type u) [Group K] [Fintype K] (W : Type v) [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ K W) : Prop :=
  ∃ l : List (Entry K), ∀ g : K, LinearMap.trace ℂ W (σ g) = lsum l g

variable {K : Type u} [Group K] [Fintype K]
variable {W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
variable (σ : Representation ℂ K W)

theorem monomial_of_finrank_zero (h : Module.finrank ℂ W = 0) : Monomial K W σ := by
  have : Subsingleton W := Module.finrank_zero_iff.1 h
  refine ⟨[], fun g => ?_⟩
  have : σ g = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
  rw [this, map_zero, lsum_nil, Pi.zero_apply]

theorem monomial_of_comm (hab : ∀ x y : K, σ x * σ y = σ y * σ x) : Monomial K W σ := by
  let T : Subgroup K := ⊤
  have hcommT : ∀ a b : T, σ a * σ b = σ b * σ a := fun a b => hab a b
  have hint := isInternal_wt σ T hcommT
  have hfin := finite_wt σ T hint
  set S := hfin.toFinset with hS
  have hSmem : ∀ χ, χ ∈ S ↔ wt σ T χ ≠ ⊥ := fun χ => by simp [hS]

  let ent : (T → ℂ) → Entry K := fun χ =>
    if hχ : wt σ T χ ≠ ⊥ then ⟨⊤, weightHom σ T hχ⟩ else ⟨⊤, 1⟩
  have hval : ∀ χ, ∀ hχ : wt σ T χ ≠ ⊥, ∀ g : K, val (ent χ) g = χ ⟨g, Subgroup.mem_top g⟩ := by
    intro χ hχ g
    have hent : ent χ = ⟨⊤, weightHom σ T hχ⟩ := by simp only [ent, dite_eq_left hχ]
    rw [hent, val]
    have hcf : ∀ x y : K, extChar ⊤ (weightHom σ T hχ) (x⁻¹ * y * x) =
        extChar ⊤ (weightHom σ T hχ) y := by
      intro x y
      simp only [extChar, dite_eq_left (Subgroup.mem_top _), weightHom_apply]
      have e : (⟨x⁻¹ * y * x, Subgroup.mem_top _⟩ : T) =
          (⟨x, Subgroup.mem_top _⟩ : T)⁻¹ * ⟨y, Subgroup.mem_top _⟩ * ⟨x, Subgroup.mem_top _⟩ := rfl
      rw [e, weight_mul σ T hχ, weight_mul σ T hχ, mul_comm (χ _) (χ ⟨y, _⟩), mul_assoc,
        ← weight_mul σ T hχ, inv_mul_cancel, weight_one σ T hχ, mul_one]
    change inducedClassFunction ⊤ (extChar ⊤ (weightHom σ T hχ)) g = _
    rw [inducedClassFunction_top_of_conj_invariant _ hcf]
    simp only [extChar, dite_eq_left (Subgroup.mem_top _), weightHom_apply]

  have htr : ∀ g : K, LinearMap.trace ℂ W (σ g) =
      ∑ χ ∈ S, χ ⟨g, Subgroup.mem_top g⟩ * (Module.finrank ℂ (wt σ T χ) : ℂ) := by
    intro g
    have hf : ∀ χ : T → ℂ, Set.MapsTo (σ g) (wt σ T χ) (wt σ T χ) :=
      fun χ => mapsTo_wt_of_comm σ T χ (σ g) (fun a => hab g a)
    rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin hf]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have hres : (σ g).restrict (hf χ) = χ ⟨g, Subgroup.mem_top g⟩ • LinearMap.id := by
      apply LinearMap.ext; intro v; apply Subtype.ext
      simp only [LinearMap.smul_apply, LinearMap.id_apply,
        Submodule.coe_smul]
      exact (mem_wt σ T χ v).1 v.2 ⟨g, Subgroup.mem_top g⟩
    rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul]

  refine ⟨(S.toList.map fun χ => List.replicate (Module.finrank ℂ (wt σ T χ)) (ent χ)).flatten,
    fun g => ?_⟩
  rw [htr g, lsum_flatten_replicate, Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [hval χ ((hSmem χ).1 hχ) g, mul_comm]

theorem monomial_of_isCompl (P₁ P₂ : Submodule ℂ W) (hc : IsCompl P₁ P₂)
    (h₁ : ∀ k : K, P₁ ≤ P₁.comap (σ k)) (h₂ : ∀ k : K, P₂ ≤ P₂.comap (σ k))
    (m₁ : Monomial K P₁ (σ.subrepresentation P₁ h₁))
    (m₂ : Monomial K P₂ (σ.subrepresentation P₂ h₂)) : Monomial K W σ := by
  obtain ⟨l₁, hl₁⟩ := m₁
  obtain ⟨l₂, hl₂⟩ := m₂
  refine ⟨l₁ ++ l₂, fun g => ?_⟩
  rw [lsum_append, Pi.add_apply, ← hl₁, ← hl₂]
  set e := Submodule.prodEquivOfIsCompl P₁ P₂ hc with he
  have : σ g =
      e.conj (((σ.subrepresentation P₁ h₁) g).prodMap ((σ.subrepresentation P₂ h₂) g)) := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply_apply]
    obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective v
    rw [LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, he,
      Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add]
    rfl
  rw [this, LinearMap.trace_conj', LinearMap.trace_prodMap']

theorem monomial_of_transitive (B : Subgroup K) [B.Normal]
    (hcommB : ∀ a b : B, σ a * σ b = σ b * σ a)
    (S : Finset (B → ℂ)) (hS : ∀ χ, χ ∈ S ↔ wt σ B χ ≠ ⊥) (χ₁ : B → ℂ) (hχ₁ : χ₁ ∈ S)
    (htrans : ∀ χ ∈ S, χ ∈ MulAction.orbit K χ₁)
    (H₁ : Subgroup K) (hH₁ : ∀ h : K, h ∈ H₁ ↔ h • χ₁ = χ₁)
    (m : Monomial H₁ (wt σ B χ₁) (stabRep σ B χ₁ H₁ (fun h hh => (hH₁ h).1 hh))) :
    Monomial K W σ := by
  obtain ⟨l', hl'⟩ := m
  refine ⟨l'.map (lift H₁), fun g => ?_⟩
  rw [← inducedClassFunction_lsum_eq]

  suffices key : ∀ Φ : K → ℂ,
      (∀ (y : K) (hy : y ∈ H₁), Φ y =
        LinearMap.trace ℂ _ (stabRep σ B χ₁ H₁ (fun h hh => (hH₁ h).1 hh) ⟨y, hy⟩)) →
      LinearMap.trace ℂ W (σ g) = inducedClassFunction H₁ Φ g by
    apply key
    intro y hy
    rw [dite_eq_left hy]
    exact (hl' ⟨y, hy⟩).symm
  intro Φ hΦ
  rw [inducedClassFunction_apply]
  have hint := isInternal_wt σ B hcommB
  have horbS : ∀ x : K, x • χ₁ ∈ S := fun x =>
    (hS _).2 ((wt_smul_ne_bot_iff σ B x χ₁).2 ((hS _).1 hχ₁))

  let D : (B → ℂ) → ℂ := fun χ => if hχ : g • χ = χ then
    LinearMap.trace ℂ (wt σ B χ) ((σ g).restrict (mapsTo_of_eq (mapsTo_smul σ B g χ) hχ)) else 0
  have hD : LinearMap.trace ℂ W (σ g) = ∑ χ ∈ S, D χ :=
    trace_eq_sum_fixed hint S (fun χ h => (hS χ).2 h) (fun χ => g • χ) (σ g) (mapsTo_smul σ B g)

  have hstep1 : ∀ x : K, (if x⁻¹ * g * x ∈ H₁ then Φ (x⁻¹ * g * x) else 0) = D (x • χ₁) := by
    intro x
    have hiff : x⁻¹ * g * x ∈ H₁ ↔ g • (x • χ₁) = x • χ₁ := by
      rw [hH₁, mul_smul, mul_smul, inv_smul_eq_iff]
    by_cases hx : x⁻¹ * g * x ∈ H₁
    · rw [ite_eq_left hx, hΦ _ hx]
      simp only [D, dite_eq_left (hiff.1 hx)]
      rw [stabRep_apply]
      exact (trace_restrict_conj σ B x g χ₁ _ _).symm
    · rw [ite_eq_right hx]
      simp only [D, dite_eq_right (mt hiff.2 hx)]

  have hstep2 : ∑ x : K, D (x • χ₁) = (Nat.card H₁ : ℂ) * ∑ χ ∈ S, D χ := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := fun x : K => x • χ₁)
      (fun x _ => horbS x) (fun x => D (x • χ₁)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have : ∑ x ∈ Finset.univ.filter (fun x : K => x • χ₁ = χ), D (x • χ₁) =
        ∑ x ∈ Finset.univ.filter (fun x : K => x • χ₁ = χ), D χ := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.1 hx).2]
    rw [this, Finset.sum_const, nsmul_eq_mul]
    congr 1
    obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.1 (htrans χ hχ)
    have hcard : Nat.card {x : K // x • χ₁ = k • χ₁} =
        (Finset.univ.filter fun x : K => x • χ₁ = k • χ₁).card := Nat.subtype_card _ (by simp)
    have hcard2 : Nat.card {x : K // x • χ₁ = k • χ₁} = Nat.card H₁ := by
      apply Nat.card_congr
      exact
        { toFun := fun x => ⟨k⁻¹ * x.1, by
            rw [hH₁, mul_smul, x.2, inv_smul_smul]⟩
          invFun := fun h => ⟨k * h.1, by
            rw [mul_smul, (hH₁ _).1 h.2]⟩
          left_inv := fun x => by simp
          right_inv := fun h => by simp }
    rw [← hcard2, hcard]

  rw [Finset.sum_congr rfl (fun x _ => hstep1 x), hstep2, hD, ← mul_assoc]
  have hne : (Nat.card H₁ : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [inv_mul_cancel₀ hne, one_mul]

/-- Every representation of a group with a normal commutative subgroup `A` with `p`-group quotient
is `Monomial`; by induction on the bound `m ≥ |K| + dim W`. -/
theorem engine {p : ℕ} (hp : p.Prime) : ∀ (m : ℕ) (K : Type u) [Group K] [Fintype K]
    (W : Type v) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ K W),
    Fintype.card K + Module.finrank ℂ W ≤ m →
    ∀ (A : Subgroup K) [A.Normal], (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ k : K, ∃ n : ℕ, k ^ p ^ n ∈ A) → Monomial K W σ := by
  intro m
  induction m with
  | zero =>
    intro K _ _ W _ _ _ σ hm
    exfalso
    have := Fintype.card_pos (α := K)
    omega
  | succ m ih =>
    intro K _ _ W _ _ _ σ hm A hAn hAcomm hpow
    by_cases hW : Module.finrank ℂ W = 0
    · exact monomial_of_finrank_zero σ hW
    by_cases hab : ∀ x y : K, σ x * σ y = σ y * σ x
    · exact monomial_of_comm σ hab

    push Not at hab
    obtain ⟨x, y, hxy⟩ := hab
    let f := σ.toHomUnits
    have hf : ∀ k, ((f k : (W →ₗ[ℂ] W)ˣ) : W →ₗ[ℂ] W) = σ k := fun k => rfl
    obtain ⟨B, hBn, hAB, hBcomm, b₀, hb₀, k₀, hbk⟩ := exists_normal_comm_not_central hp A hpow f
      (fun a ha b hb => Units.ext (by
        simp only [hf, ← map_mul, hAcomm a ha b hb]))
      ⟨x, y, fun h => hxy (by simpa [hf] using congrArg Units.val h)⟩
    have := hBn
    have hcommB : ∀ a b : B, σ a * σ b = σ b * σ a := fun a b => by
      simpa [hf] using congrArg Units.val (hBcomm a a.2 b b.2)
    have hbk' : σ b₀ * σ k₀ ≠ σ k₀ * σ b₀ := fun h => hbk (Units.ext (by simpa [hf] using h))
    have hint := isInternal_wt σ B hcommB
    have hfin := finite_wt σ B hint
    set S := hfin.toFinset with hS
    have hSmem : ∀ χ, χ ∈ S ↔ wt σ B χ ≠ ⊥ := fun χ => by simp [hS]

    have hW' : Nontrivial W := Module.finrank_pos_iff.1 (Nat.pos_of_ne_zero hW)
    obtain ⟨χ₁, hχ₁⟩ : ∃ χ₁, χ₁ ∈ S := by
      by_contra hnone
      push Not at hnone
      have htop := hint.submodule_iSup_eq_top
      have : (⨆ χ, wt σ B χ) = ⊥ := by
        apply iSup_eq_bot.2
        intro χ
        by_contra hne
        exact hnone χ ((hSmem χ).2 hne)
      rw [this] at htop
      exact bot_ne_top htop
    obtain ⟨χ₂, hχ₂, hne⟩ : ∃ χ₂ ∈ S, χ₂ ≠ χ₁ := by
      by_contra hall
      push Not at hall
      have htop : wt σ B χ₁ = ⊤ := by
        rw [eq_top_iff, ← hint.submodule_iSup_eq_top]
        apply iSup_le
        intro χ
        by_cases hχ : wt σ B χ = ⊥
        · rw [hχ]; exact bot_le
        · rw [hall χ ((hSmem χ).2 hχ)]
      apply hbk'
      apply LinearMap.ext
      intro v
      have hv : ∀ w : W, σ b₀ w = χ₁ ⟨b₀, hb₀⟩ • w := fun w =>
        (mem_wt σ B χ₁ w).1 (htop ▸ Submodule.mem_top) ⟨b₀, hb₀⟩
      simp only [Module.End.mul_apply, hv, map_smul]
    by_cases htr : ∀ χ ∈ S, χ ∈ MulAction.orbit K χ₁
    ·
      obtain ⟨H₁, hH₁⟩ : ∃ H₁ : Subgroup K, ∀ h : K, h ∈ H₁ ↔ h • χ₁ = χ₁ :=
        ⟨MulAction.stabilizer K χ₁, fun h => MulAction.mem_stabilizer_iff⟩
      have hH₁top : H₁ ≠ ⊤ := by
        intro htopH
        obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.1 (htr χ₂ hχ₂)
        apply hne
        have : k ∈ H₁ := htopH ▸ Subgroup.mem_top k
        exact (hH₁ k).1 this
      have hcard : Fintype.card H₁ < Fintype.card K := by
        have h1 := Subgroup.card_mul_index H₁
        have h2 := Subgroup.one_lt_index_of_ne_top hH₁top
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h1
        have h3 := Fintype.card_pos (α := H₁)
        nlinarith
      have hdim : Module.finrank ℂ (wt σ B χ₁) ≤ Module.finrank ℂ W := Submodule.finrank_le _
      apply monomial_of_transitive σ B hcommB S hSmem χ₁ hχ₁ htr H₁ hH₁
      apply ih (↥H₁) (wt σ B χ₁) (stabRep σ B χ₁ H₁ fun h hh => (hH₁ h).1 hh) (by omega)
        (A.subgroupOf H₁)
      · intro a ha b hb
        apply Subtype.ext
        exact hAcomm a ha b hb
      · intro h
        obtain ⟨n, hn⟩ := hpow h
        exact ⟨n, by rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]; exact hn⟩
    ·
      push Not at htr
      obtain ⟨χ₃, hχ₃, hno⟩ := htr
      let O := MulAction.orbit K χ₁
      let P₁ : Submodule ℂ W := ⨆ χ ∈ O, wt σ B χ
      let P₂ : Submodule ℂ W := ⨆ χ ∈ Oᶜ, wt σ B χ
      have hc : IsCompl P₁ P₂ := by
        constructor
        · exact hint.submodule_iSupIndep.disjoint_biSup_biSup disjoint_compl_right
        · rw [codisjoint_iff]
          have : P₁ ⊔ P₂ = ⨆ χ, wt σ B χ := by
            change (⨆ χ ∈ O, wt σ B χ) ⊔ (⨆ χ ∈ Oᶜ, wt σ B χ) = _
            rw [← iSup_union, Set.union_compl_self, iSup_univ]
          rw [this, hint.submodule_iSup_eq_top]
      have hstab : ∀ (T : Set (B → ℂ)), (∀ k : K, ∀ χ ∈ T, k • χ ∈ T) →
          ∀ k : K, (⨆ χ ∈ T, wt σ B χ) ≤ (⨆ χ ∈ T, wt σ B χ).comap (σ k) := by
        intro T hT k
        rw [← Submodule.map_le_iff_le_comap, Submodule.map_iSup]
        apply iSup_le
        intro χ
        rw [Submodule.map_iSup]
        apply iSup_le
        intro hχ
        refine le_trans ?_ (le_biSup (fun χ => wt σ B χ) (hT k χ hχ))
        rintro _ ⟨v, hv, rfl⟩
        exact mapsTo_smul σ B k χ hv
      have hO : ∀ k : K, ∀ χ ∈ O, k • χ ∈ O := by
        intro k χ hχ
        obtain ⟨j, rfl⟩ := MulAction.mem_orbit_iff.1 hχ
        exact MulAction.mem_orbit_iff.2 ⟨k * j, mul_smul k j χ₁⟩
      have hOc : ∀ k : K, ∀ χ ∈ Oᶜ, k • χ ∈ Oᶜ := by
        intro k χ hχ hk
        apply hχ
        have := hO k⁻¹ _ hk
        rwa [inv_smul_smul] at this
      have h₁ := hstab O hO
      have h₂ := hstab Oᶜ hOc
      have hP₁ : P₁ ≠ ⊥ := by
        intro hbot
        apply (hSmem χ₁).1 hχ₁
        rw [eq_bot_iff, ← hbot]
        exact le_biSup (fun χ => wt σ B χ) (MulAction.mem_orbit_self χ₁)
      have hP₂ : P₂ ≠ ⊥ := by
        intro hbot
        apply (hSmem χ₃).1 hχ₃
        rw [eq_bot_iff, ← hbot]
        exact le_biSup (fun χ => wt σ B χ) hno
      have hsum := Submodule.finrank_add_eq_of_isCompl hc
      have hp1 : 0 < Module.finrank ℂ P₁ :=
        Nat.pos_of_ne_zero (fun h => hP₁ (Submodule.finrank_eq_zero.1 h))
      have hp2 : 0 < Module.finrank ℂ P₂ :=
        Nat.pos_of_ne_zero (fun h => hP₂ (Submodule.finrank_eq_zero.1 h))
      apply monomial_of_isCompl σ P₁ P₂ hc h₁ h₂
      · exact ih K P₁ (σ.subrepresentation P₁ h₁) (by omega) A hAcomm hpow
      · exact ih K P₂ (σ.subrepresentation P₂ h₂) (by omega) A hAcomm hpow

end Induction

section Final

variable {G : Type u} [Group G] [Fintype G] {n : ℕ}

/-- A matrix representation as a representation on `Fin n → ℂ`. -/
def repOfGL (ρ : G →* GL (Fin n) ℂ) : Representation ℂ G (Fin n → ℂ) where
  toFun g := Matrix.toLin' ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  map_one' := by
    rw [map_one, Units.val_one, Matrix.toLin'_one]
    rfl
  map_mul' x y := by
    rw [map_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl

omit [Fintype G] in
theorem repOfGL_apply (ρ : G →* GL (Fin n) ℂ) (g : G) :
    repOfGL ρ g = Matrix.toLin' ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := rfl

omit [Fintype G] in
theorem trace_repOfGL (ρ : G →* GL (Fin n) ℂ) (g : G) :
    LinearMap.trace ℂ _ (repOfGL ρ g) =
      ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace := by
  rw [repOfGL_apply, LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']


end Final

open scoped Classical MatrixGroups in
/-- **The monomial case.** Let `G` be a finite group with a normal commutative subgroup `A` such
that every element has a `p`-power in `A`, for a prime `p`. Then the trace of every complex matrix
representation of `G` is a sum (with nonnegative integer multiplicities) of class functions induced
from linear characters of subgroups. -/
theorem exists_trace_eq_sum_inducedClassFunction_linearCharacter
    {G : Type u} [Group G] [Fintype G] {p : ℕ} (hp : p.Prime) (A : Subgroup G) (hA : A.Normal)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hquot : ∀ g : G, ∃ n : ℕ, g ^ p ^ n ∈ A)
    {n : ℕ} (ρ : G →* GL (Fin n) ℂ) :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)),
      ∀ g : G, ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
        ∑ i : Fin k, inducedClassFunction (H i)
          (fun x => if hx : x ∈ H i then (((ψ i) ⟨x, hx⟩ : ℂˣ) : ℂ) else 0) g := by
  have := hA
  obtain ⟨l, hl⟩ := engine hp _ G (Fin n → ℂ) (repOfGL ρ) le_rfl A hcomm hquot
  refine ⟨l.length, fun i => (l.get i).1, fun i => (l.get i).2, fun g => ?_⟩
  rw [← trace_repOfGL, hl g, lsum]
  conv_lhs => rw [← List.ofFn_get l, List.map_ofFn, List.sum_ofFn]
  rfl


end Langlands.FiniteRep.MonomialTrace

end
