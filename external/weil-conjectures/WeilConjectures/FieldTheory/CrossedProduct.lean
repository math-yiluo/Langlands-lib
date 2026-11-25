/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import WeilConjectures.FieldTheory.Cr

/-!
# Crossed products and Galois 2-cocycles over `C₁` fields

Let `L / K` be a finite Galois extension with group `G` and let `f : G → G → Lˣ` be an
(inhomogeneous) 2-cocycle. The *crossed product* `(L, G, f)` is the `K`-algebra with `L`-basis
`(u_σ)_{σ ∈ G}` and relations `u_σ x = σ(x) u_σ`, `u_σ u_τ = f(σ, τ) u_{στ}`.

We realise it concretely as the `K`-subalgebra `CrossedProduct.subalgebra f hf` of
`Module.End K (G → L)` spanned by the operators `x • u_σ` of its left regular representation,
which spares us from verifying the ring axioms by hand. It is a central simple `K`-algebra of
dimension `[L : K] ^ 2`.

## Main statements

- `CrossedProduct.isSimpleRing`, `CrossedProduct.isCentral`: the crossed product is central
  simple.
- `CrossedProduct.finrank_eq`: it has dimension `[L : K] ^ 2`.
- `IsQuasiAlgClosed.exists_mul_eq_of_galois_cocycle`: over a `C₁` field every Galois 2-cocycle
  is a coboundary, i.e. `H²(Gal(L/K), Lˣ) = 0`.
-/

@[expose] public section

universe u

open Module

namespace CrossedProduct

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  (f : (L ≃ₐ[K] L) → (L ≃ₐ[K] L) → Lˣ)

/-- Left multiplication by elements of `L` on `G → L`, as a `K`-algebra map. -/
abbrev lam : L →ₐ[K] Module.End K ((L ≃ₐ[K] L) → L) := Algebra.lsmul K K _

lemma lam_apply (x : L) (a : (L ≃ₐ[K] L) → L) (ρ : L ≃ₐ[K] L) : lam x a ρ = x * a ρ := rfl

/-- The operator `u_σ` of the left regular representation of the crossed product on `G → L`. -/
noncomputable def twist (σ : L ≃ₐ[K] L) : Module.End K ((L ≃ₐ[K] L) → L) where
  toFun a ρ := σ (a (σ⁻¹ * ρ)) * f σ (σ⁻¹ * ρ)
  map_add' a b := by ext ρ; simp [add_mul]
  map_smul' k a := by ext ρ; simp

lemma twist_apply (σ : L ≃ₐ[K] L) (a : (L ≃ₐ[K] L) → L) (ρ : L ≃ₐ[K] L) :
    twist f σ a ρ = σ (a (σ⁻¹ * ρ)) * f σ (σ⁻¹ * ρ) := rfl

lemma twist_mul_lam (σ : L ≃ₐ[K] L) (x : L) :
    twist f σ * lam x = lam (σ x) * twist f σ :=
  LinearMap.ext fun a => funext fun ρ => by
    simp only [Module.End.mul_apply, twist_apply, lam_apply, map_mul, mul_assoc]

variable {f}

section Cocycle

variable (hf : ∀ σ τ ρ, (f σ τ : L) * f (σ * τ) ρ = σ (f τ ρ : L) * f σ (τ * ρ))
include hf

lemma cocycle_one_left (ρ : L ≃ₐ[K] L) : (f 1 ρ : L) = f 1 1 := by
  have h := hf 1 1 ρ
  simp only [one_mul, AlgEquiv.one_apply] at h
  exact (mul_right_cancel₀ (Units.ne_zero (f 1 ρ)) h).symm

lemma twist_one : twist f 1 = lam (f 1 1 : L) :=
  LinearMap.ext fun a => funext fun ρ => by
    simp [twist_apply, lam_apply, cocycle_one_left hf, mul_comm]

lemma twist_mul_twist (σ τ : L ≃ₐ[K] L) :
    twist f σ * twist f τ = lam (f σ τ : L) * twist f (σ * τ) :=
  LinearMap.ext fun a => funext fun ρ => by
    obtain ⟨ν, rfl⟩ : ∃ ν, ρ = σ * τ * ν := ⟨(σ * τ)⁻¹ * ρ, by simp [mul_assoc]⟩
    simp only [Module.End.mul_apply, twist_apply, lam_apply, mul_assoc, mul_inv_rev,
      inv_mul_cancel_left, map_mul, AlgEquiv.mul_apply]
    linear_combination (-(σ (τ (a ν)))) * hf σ τ ν

end Cocycle

variable [FiniteDimensional K L]

variable (f) in
/-- The left regular representation `a ↦ ∑_σ a_σ u_σ` of the crossed product. -/
noncomputable def toEnd : ((L ≃ₐ[K] L) → L) →ₗ[K] Module.End K ((L ≃ₐ[K] L) → L) where
  toFun a := ∑ σ, lam (a σ) * twist f σ
  map_add' a b := by simp [Finset.sum_add_distrib, add_mul]
  map_smul' k a := by simp [Finset.smul_sum]

lemma toEnd_apply (a : (L ≃ₐ[K] L) → L) : toEnd f a = ∑ σ, lam (a σ) * twist f σ := rfl

variable [DecidableEq (L ≃ₐ[K] L)] in
lemma toEnd_single (σ : L ≃ₐ[K] L) (x : L) :
    toEnd f (Pi.single σ x) = lam x * twist f σ := by
  rw [toEnd_apply, Finset.sum_eq_single σ (fun τ _ hτ => by simp [Pi.single_eq_of_ne hτ])
    (by simp)]
  simp

variable [DecidableEq (L ≃ₐ[K] L)] in
lemma toEnd_apply_single_one (a : (L ≃ₐ[K] L) → L) (ρ : L ≃ₐ[K] L) :
    toEnd f a (Pi.single 1 1) ρ = a ρ * f ρ 1 := by
  rw [toEnd_apply, LinearMap.sum_apply, Finset.sum_apply,
    Finset.sum_eq_single ρ]
  · simp [lam_apply, twist_apply]
  · intro σ _ hσ
    have : σ⁻¹ * ρ ≠ 1 := fun h => hσ (inv_mul_eq_one.mp h)
    simp [lam_apply, twist_apply, Pi.single_eq_of_ne this]
  · simp

lemma toEnd_injective : Function.Injective (toEnd f) := fun a b h => funext fun ρ => by
  classical
  have := congrArg (fun T => T (Pi.single 1 1) ρ) h
  simp only [toEnd_apply_single_one] at this
  exact mul_right_cancel₀ (Units.ne_zero _) this

lemma lam_mul_toEnd (b : L) (a : (L ≃ₐ[K] L) → L) :
    lam b * toEnd f a = toEnd f (fun ρ => b * a ρ) := by
  simp only [toEnd_apply, Finset.mul_sum, ← mul_assoc, ← map_mul]

lemma toEnd_mul_lam (a : (L ≃ₐ[K] L) → L) (b : L) :
    toEnd f a * lam b = toEnd f (fun ρ => a ρ * ρ b) := by
  simp only [toEnd_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun σ _ => by
    rw [mul_assoc, twist_mul_lam, ← mul_assoc, ← map_mul]

lemma lam_mul_twist_mem (x : L) (σ : L ≃ₐ[K] L) :
    lam x * twist f σ ∈ LinearMap.range (toEnd f) :=
  by classical exact ⟨Pi.single σ x, toEnd_single σ x⟩

variable (hf : ∀ σ τ ρ, (f σ τ : L) * f (σ * τ) ρ = σ (f τ ρ : L) * f σ (τ * ρ))

omit [FiniteDimensional K L] in
include hf in
lemma lam_eq (x : L) : lam x = lam (x * ((f 1 1)⁻¹ : Lˣ)) * twist f 1 := by
  rw [twist_one hf, ← map_mul, mul_assoc, Units.inv_mul, mul_one]

omit [FiniteDimensional K L] in
include hf in
lemma lam_mul_twist_mul_lam_mul_twist (x y : L) (σ τ : L ≃ₐ[K] L) :
    lam x * twist f σ * (lam y * twist f τ) =
      lam (x * σ y * f σ τ) * twist f (σ * τ) := by
  calc lam x * twist f σ * (lam y * twist f τ)
      = lam x * ((twist f σ * lam y) * twist f τ) := by simp only [mul_assoc]
    _ = lam x * (lam (σ y) * (twist f σ * twist f τ)) := by rw [twist_mul_lam, mul_assoc]
    _ = _ := by rw [twist_mul_twist hf]; simp only [map_mul, mul_assoc]

variable (f) in
include hf in
/-- The crossed product `(L, Gal(L/K), f)` of a Galois 2-cocycle `f`, realised as the
`K`-subalgebra of `Module.End K (G → L)` given by its left regular representation. -/
noncomputable def subalgebra : Subalgebra K (Module.End K ((L ≃ₐ[K] L) → L)) :=
  (LinearMap.range (toEnd f)).toSubalgebra
    (by rw [← map_one (lam (L := L) (K := K)), lam_eq hf]; exact lam_mul_twist_mem _ _)
    (by
      rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      rw [toEnd_apply, toEnd_apply, Finset.sum_mul_sum]
      refine Submodule.sum_mem _ fun σ _ => Submodule.sum_mem _ fun τ _ => ?_
      rw [lam_mul_twist_mul_lam_mul_twist hf]
      exact lam_mul_twist_mem _ _)

lemma mem_subalgebra_iff (T : Module.End K ((L ≃ₐ[K] L) → L)) :
    T ∈ subalgebra f hf ↔ T ∈ LinearMap.range (toEnd f) := Iff.rfl

/-- The embedding of `L` into the crossed product. -/
noncomputable def ι : L →ₐ[K] subalgebra f hf :=
  lam.codRestrict _ fun x => by
    rw [mem_subalgebra_iff, lam_eq hf]; exact lam_mul_twist_mem _ _

/-- The basis element `u_σ` of the crossed product. -/
noncomputable def gen (σ : L ≃ₐ[K] L) : subalgebra f hf :=
  ⟨twist f σ, by
    rw [mem_subalgebra_iff, ← one_mul (twist f σ), ← map_one lam]
    exact lam_mul_twist_mem _ _⟩

/-- The `K`-linear isomorphism `(G → L) → (L, G, f)`, `a ↦ ∑_σ a_σ u_σ`. -/
noncomputable def mk : ((L ≃ₐ[K] L) → L) →ₗ[K] subalgebra f hf :=
  (toEnd f).codRestrict (Subalgebra.toSubmodule (subalgebra f hf)) fun a => ⟨a, rfl⟩

lemma gen_mul_ι (σ : L ≃ₐ[K] L) (x : L) : gen hf σ * ι hf x = ι hf (σ x) * gen hf σ :=
  Subtype.ext (twist_mul_lam f σ x)

lemma gen_mul_gen (σ τ : L ≃ₐ[K] L) : gen hf σ * gen hf τ = ι hf (f σ τ) * gen hf (σ * τ) :=
  Subtype.ext (twist_mul_twist hf σ τ)

lemma gen_one : gen hf 1 = ι hf (f 1 1) := Subtype.ext (twist_one hf)

variable [DecidableEq (L ≃ₐ[K] L)] in
lemma mk_single (σ : L ≃ₐ[K] L) (x : L) : mk hf (Pi.single σ x) = ι hf x * gen hf σ :=
  Subtype.ext (toEnd_single σ x)

lemma mk_injective : Function.Injective (mk hf) := fun _ _ h =>
  toEnd_injective (congrArg Subtype.val h)

lemma mk_surjective : Function.Surjective (mk hf) := by
  rintro ⟨_, a, rfl⟩
  exact ⟨a, rfl⟩

lemma ι_mul_mk (b : L) (a : (L ≃ₐ[K] L) → L) :
    ι hf b * mk hf a = mk hf (fun ρ => b * a ρ) :=
  Subtype.ext (lam_mul_toEnd b a)

lemma mk_mul_ι (a : (L ≃ₐ[K] L) → L) (b : L) :
    mk hf a * ι hf b = mk hf (fun ρ => a ρ * ρ b) :=
  Subtype.ext (toEnd_mul_lam a b)

/-- `u_σ⁻¹ u_σ` is a nonzero element of `L`. -/
lemma gen_inv_mul_gen (σ : L ≃ₐ[K] L) :
    gen hf σ⁻¹ * gen hf σ = ι hf ((f σ⁻¹ σ : L) * f 1 1) := by
  rw [gen_mul_gen, inv_mul_cancel, gen_one, map_mul]

/-- The crossed product has dimension `[L : K] ^ 2` over `K`. -/
theorem finrank_eq [IsGalois K L] :
    finrank K (subalgebra f hf) = finrank K L * finrank K L := by
  rw [← (LinearEquiv.ofBijective (mk hf) ⟨mk_injective hf, mk_surjective hf⟩).finrank_eq,
    Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]

/-- The crossed product of a Galois 2-cocycle is a simple ring. -/
theorem isSimpleRing : IsSimpleRing (subalgebra f hf) := by
  classical
  refine .of_eq_bot_or_eq_top fun I => or_iff_not_imp_left.mpr fun hI => ?_
  obtain ⟨s, hsI, hs0⟩ : ∃ s ∈ I, s ≠ 0 := by
    by_contra! h
    exact hI (eq_bot_iff.mpr fun s hs => by simpa using h s hs)
  have hex : ∃ k, ∃ a, mk hf a ∈ I ∧ a ≠ 0 ∧
      (Finset.univ.filter fun ρ => a ρ ≠ 0).card = k := by
    obtain ⟨a, rfl⟩ := mk_surjective hf s
    exact ⟨_, a, hsI, by rintro rfl; exact hs0 (map_zero _), rfl⟩
  obtain ⟨a, haI, ha0, hak⟩ := Nat.find_spec hex
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ, a ρ ≠ 0 := by
    by_contra! h
    exact ha0 (funext h)
  have hsingle : ∀ ρ, ρ ≠ ρ₀ → a ρ = 0 := by
    intro ρ₁ hne
    by_contra h1
    obtain ⟨b, hb⟩ : ∃ b, ρ₁ b ≠ ρ₀ b := by
      by_contra! h
      exact hne (AlgEquiv.ext h)
    let a' := fun ρ : L ≃ₐ[K] L => (ρ₀ b - ρ b) * a ρ
    have ha'I : mk hf a' ∈ I := by
      have : mk hf a' = ι hf (ρ₀ b) * mk hf a - mk hf a * ι hf b := by
        rw [ι_mul_mk, mk_mul_ι, ← map_sub]
        congr 1
        funext ρ
        simp only [a', Pi.sub_apply]
        ring
      rw [this]
      exact I.sub_mem (I.mul_mem_left _ _ haI) (I.mul_mem_right _ _ haI)
    have ha'0 : a' ≠ 0 := fun h =>
      mul_ne_zero (sub_ne_zero.mpr hb.symm) h1 (congrFun h ρ₁)
    have hsub : (Finset.univ.filter fun ρ => a' ρ ≠ 0) ⊆
        Finset.univ.filter fun ρ => a ρ ≠ 0 := by
      intro ρ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact right_ne_zero_of_mul
    have hcard : (Finset.univ.filter fun ρ => a' ρ ≠ 0).card < Nat.find hex := by
      rw [← hak]
      refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨ρ₀, ?_, ?_⟩)
      · simpa using hρ₀
      · simp [a']
    exact Nat.find_min hex hcard ⟨a', ha'I, ha'0, rfl⟩
  have ha : a = Pi.single ρ₀ (a ρ₀) := funext fun ρ => by
    by_cases h : ρ = ρ₀
    · subst h; simp
    · simp [h, hsingle ρ h]
  rw [ha, mk_single] at haI
  set x := a ρ₀ * (f ρ₀ ρ₀⁻¹ : L) * f 1 1 with hx
  have hx0 : x ≠ 0 := mul_ne_zero (mul_ne_zero hρ₀ (Units.ne_zero _)) (Units.ne_zero _)
  have h1 : ι hf (a ρ₀) * gen hf ρ₀ * gen hf ρ₀⁻¹ = ι hf x := by
    rw [mul_assoc, gen_mul_gen, mul_inv_cancel, gen_one, ← mul_assoc, ← map_mul, ← map_mul]
  have h2 : ι hf x⁻¹ * ι hf x = 1 := by rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  rw [← I.one_mem_iff, ← h2, ← h1]
  exact I.mul_mem_left _ _ (I.mul_mem_right _ _ haI)

/-- The crossed product of a Galois 2-cocycle is a central `K`-algebra. -/
theorem isCentral [IsGalois K L] : Algebra.IsCentral K (subalgebra f hf) := by
  classical
  refine ⟨fun z hz => ?_⟩
  rw [Subalgebra.mem_center_iff] at hz
  obtain ⟨a, rfl⟩ := mk_surjective hf z
  have h1 : ∀ b ρ, b * a ρ = a ρ * ρ b := fun b ρ => by
    have := hz (ι hf b)
    rw [ι_mul_mk, mk_mul_ι] at this
    exact congrFun (mk_injective hf this) ρ
  have h2 : ∀ ρ, ρ ≠ 1 → a ρ = 0 := by
    intro ρ hρ
    obtain ⟨b, hb⟩ : ∃ b, ρ b ≠ b := by
      by_contra! h
      exact hρ (AlgEquiv.ext h)
    have := h1 b ρ
    have h : (ρ b - b) * a ρ = 0 := by linear_combination -this
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hb)
  have ha : a = Pi.single 1 (a 1) := funext fun ρ => by
    by_cases h : ρ = 1
    · subst h; simp
    · simp [h, h2 ρ h]
  have hax : mk hf a = ι hf (a 1 * f 1 1) := by
    rw [ha, mk_single, gen_one, ← map_mul, Pi.single_eq_same]
  rw [hax] at hz ⊢
  have h3 : ∀ σ : L ≃ₐ[K] L, σ (a 1 * f 1 1) = a 1 * f 1 1 := fun σ => by
    have := hz (gen hf σ)
    rw [gen_mul_ι, ← mk_single, ← mk_single] at this
    simpa using congrFun (mk_injective hf this) σ
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed _).mpr h3)
  rw [← hk, AlgHom.commutes]
  exact Subalgebra.algebraMap_mem _ k

end CrossedProduct

open CrossedProduct in
/-- Over a quasi-algebraically closed (`C₁`) field `K`, every inhomogeneous 2-cocycle of a finite
Galois extension `L / K` with values in `Lˣ` is a coboundary: `H²(Gal(L/K), Lˣ) = 0`. The crossed
product is a central simple `K`-algebra of dimension `[L : K] ^ 2`, hence a matrix algebra
`M_n(K)` with `n = [L : K]`; on its simple module `Kⁿ`, which is a line over `L`, the basis
elements `u_σ` act by scalars `c_σ` that split `f`.
(blueprint: `lemma-cohomology-multiplicative-group--7`, crossed product step) -/
theorem IsQuasiAlgClosed.exists_mul_eq_of_galois_cocycle (K L : Type u) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsQuasiAlgClosed K]
    (f : (L ≃ₐ[K] L) → (L ≃ₐ[K] L) → Lˣ)
    (hf : ∀ σ τ ρ, (f σ τ : L) * f (σ * τ) ρ = σ (f τ ρ : L) * f σ (τ * ρ)) :
    ∃ c : (L ≃ₐ[K] L) → Lˣ, ∀ σ τ, (f σ τ : L) * c (σ * τ) = σ (c τ : L) * c σ := by
  set S := subalgebra f hf
  have := isSimpleRing hf
  have := isCentral hf
  have := IsArtinianRing.of_finite K S
  obtain ⟨m, hm, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K S
  have : Algebra.IsCentral K D := Algebra.IsCentral.of_algEquiv_matrix e
  let g : K ≃ₐ[K] D := AlgEquiv.ofBijective (Algebra.ofId K D) <| by
    refine ⟨(algebraMap K D).injective, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (Algebra.ofId K D).toLinearMap)
      (by rw [Module.finrank_self, finrank_eq_one_of_isCentral K D])).mp
      (algebraMap K D).injective
  let e' : S ≃ₐ[K] Matrix (Fin m) (Fin m) K := e.trans g.symm.mapMatrix
  let ψ : S →ₐ[K] Module.End K (Fin m → K) := (e'.trans Matrix.toLinAlgEquiv').toAlgHom
  -- dimension count: `m = [L : K]`
  have hmn : m = finrank K L := by
    have h := finrank_eq (f := f) hf
    rw [e'.toLinearEquiv.finrank_eq, Module.finrank_matrix] at h
    simp only [Fintype.card_fin, Module.finrank_self, mul_one] at h
    exact Nat.mul_self_inj.mp h
  -- `Kᵐ` as an `L`-vector space via `ι`
  let θ : L →+* Module.End K (Fin m → K) := (ψ.comp (ι hf)).toRingHom
  let : Module L (Fin m → K) := Module.compHom _ θ
  have hsmul : ∀ (x : L) (w : Fin m → K), x • w = ψ (ι hf x) w := fun _ _ => rfl
  have : IsScalarTower K L (Fin m → K) := ⟨fun k x w => by
    rw [hsmul, map_smul, map_smul]
    rfl⟩
  have hrank : finrank L (Fin m → K) = 1 := by
    have h := Module.finrank_mul_finrank K L (Fin m → K)
    rw [Module.finrank_fin_fun, ← hmn] at h
    have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact Nat.eq_of_mul_eq_mul_left hm0 (h.trans (mul_one m).symm)
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin m → K)
  have hspan := (finrank_eq_one_iff_of_nonzero' v hv).mp hrank
  choose c hc using fun σ => hspan (ψ (gen hf σ) v)
  have hc0 : ∀ σ, c σ ≠ 0 := by
    intro σ h
    have h0 : ψ (gen hf σ) v = 0 := by rw [← hc, h, zero_smul]
    have : ((f σ⁻¹ σ : L) * f 1 1) • v = 0 := by
      rw [hsmul, ← gen_inv_mul_gen, map_mul, Module.End.mul_apply, h0, map_zero]
    exact hv ((smul_eq_zero.mp this).resolve_left
      (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)))
  refine ⟨fun σ => Units.mk0 (c σ) (hc0 σ), fun σ τ => ?_⟩
  simp only [Units.val_mk0]
  refine smul_left_injective L hv ?_
  simp only
  calc ((f σ τ : L) * c (σ * τ)) • v = ψ (ι hf (f σ τ) * gen hf (σ * τ)) v := by
        rw [mul_smul, hc, hsmul, map_mul, Module.End.mul_apply]
    _ = ψ (gen hf σ) (ψ (ι hf (c τ)) v) := by
        rw [← gen_mul_gen, map_mul, Module.End.mul_apply, ← hc, hsmul]
    _ = (σ (c τ) * c σ) • v := by
        rw [← Module.End.mul_apply, ← map_mul, gen_mul_ι, map_mul, Module.End.mul_apply, ← hc,
          ← hsmul, mul_smul]
