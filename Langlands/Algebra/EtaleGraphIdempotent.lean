import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Tactic.LinearCombination

/-! # Graph idempotents of algebra maps out of an unramified algebra -/

noncomputable section

universe u v w w'

open TensorProduct Algebra.TensorProduct

namespace Langlands.Algebra.GraphIdempotent


section Idempotent

variable {S : Type*} [CommRing S]

theorem mul_eq_zero_of_mem_span {e x : S} (he : IsIdempotentElem e)
    (hx : x ∈ Ideal.span {1 - e}) : x * e = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  have he' : e * e = e := he.eq
  linear_combination (-a) * he'

theorem eq_zero_of_mem_span_of_mem_span {e x : S} (he : IsIdempotentElem e)
    (h₁ : x ∈ Ideal.span {1 - e}) (h₂ : x ∈ Ideal.span {e}) : x = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp h₂
  have h0 := mul_eq_zero_of_mem_span he h₁
  have he' : e * e = e := he.eq
  linear_combination h0 - a * he'

theorem span_ne_top_of_ne_one {s : S} (hs : IsIdempotentElem s) (h1 : s ≠ 1) :
    Ideal.span {s} ≠ ⊤ := by
  intro htop
  rw [Ideal.span_singleton_eq_top] at htop
  obtain ⟨u, hu⟩ := htop
  apply h1
  have hs' : s * s = s := hs.eq
  calc s = s * (↑u * ↑u⁻¹) := by rw [Units.mul_inv, mul_one]
    _ = (s * s) * ↑u⁻¹ := by rw [← hu]; ring
    _ = s * ↑u⁻¹ := by rw [hs']
    _ = 1 := by rw [← hu, Units.mul_inv]

end Idempotent

section General

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

section Basic

variable {T : Type w} [CommRing T] [Algebra A T]

/-- The multiplication map `μ_φ : B ⊗_A T → T`, `b ⊗ t ↦ φ b * t`, of an algebra map `φ`. -/
abbrev graphMul (φ : B →ₐ[A] T) : B ⊗[A] T →ₐ[A] T :=
  productMap φ (AlgHom.id A T)

/-- `e` is the graph idempotent of `φ`: an idempotent with `μ_φ e = 1` such that
`(b ⊗ 1) e = (1 ⊗ φ b) e` for all `b`. -/
structure IsGraphIdempotent (φ : B →ₐ[A] T) (e : B ⊗[A] T) : Prop where
  isIdempotentElem : IsIdempotentElem e
  graphMul_eq_one : graphMul φ e = 1
  tmul_one_mul : ∀ b : B, (b ⊗ₜ[A] (1 : T)) * e = ((1 : B) ⊗ₜ[A] φ b) * e

theorem mul_eq_of_tmul_one_mul {φ : B →ₐ[A] T} {e : B ⊗[A] T}
    (h : ∀ b : B, (b ⊗ₜ[A] (1 : T)) * e = ((1 : B) ⊗ₜ[A] φ b) * e) (x : B ⊗[A] T) :
    x * e = ((1 : B) ⊗ₜ[A] graphMul φ x) * e := by
  induction x with
  | tmul b t =>
    calc (b ⊗ₜ[A] t) * e = ((1 : B) ⊗ₜ[A] t) * ((b ⊗ₜ[A] (1 : T)) * e) := by
          rw [← mul_assoc, tmul_mul_tmul, one_mul, mul_one]
      _ = ((1 : B) ⊗ₜ[A] t) * (((1 : B) ⊗ₜ[A] φ b) * e) := by rw [h b]
      _ = ((1 : B) ⊗ₜ[A] (φ b * t)) * e := by
          rw [← mul_assoc, tmul_mul_tmul, one_mul, mul_comm t]
      _ = ((1 : B) ⊗ₜ[A] graphMul φ (b ⊗ₜ[A] t)) * e := by
          rw [productMap_apply_tmul, AlgHom.id_apply]
  | add x y hx hy => rw [add_mul, hx, hy, map_add, tmul_add, add_mul]

namespace IsGraphIdempotent

variable {φ ψ : B →ₐ[A] T} {e f : B ⊗[A] T}

theorem mul_eq (he : IsGraphIdempotent φ e) (x : B ⊗[A] T) :
    x * e = ((1 : B) ⊗ₜ[A] graphMul φ x) * e :=
  mul_eq_of_tmul_one_mul he.tmul_one_mul x

/-- Graph idempotents are unique. -/
theorem unique (he : IsGraphIdempotent φ e) (hf : IsGraphIdempotent φ f) : e = f := by
  have h1 : e * f = f := by rw [hf.mul_eq e, he.graphMul_eq_one, ← one_def, one_mul]
  have h2 : f * e = e := by rw [he.mul_eq f, hf.graphMul_eq_one, ← one_def, one_mul]
  calc e = f * e := h2.symm
    _ = e * f := mul_comm _ _
    _ = f := h1

/-- A graph idempotent determines its algebra map. -/
theorem algHom_eq (he : IsGraphIdempotent φ e) (hψ : IsGraphIdempotent ψ e) : φ = ψ := by
  ext b
  have h := congrArg (graphMul ψ) (he.tmul_one_mul b)
  rw [map_mul, map_mul, hψ.graphMul_eq_one, productMap_apply_tmul, productMap_apply_tmul,
    AlgHom.id_apply, AlgHom.id_apply, map_one] at h
  simpa using h.symm

/-- Elements below a graph idempotent are determined by their image under `μ_φ`. -/
theorem eq_mul_of_mul_eq (he : IsGraphIdempotent φ e) (hf : f * e = f) :
    f = e * ((1 : B) ⊗ₜ[A] graphMul φ f) := by
  rw [mul_comm, ← he.mul_eq f, hf]

theorem ne_zero [Nontrivial T] (he : IsGraphIdempotent φ e) : e ≠ 0 := by
  intro h
  have := he.graphMul_eq_one
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem graphMul_map {T' : Type w'} [CommRing T'] [Algebra A T'] (χ : T →ₐ[A] T')
    (x : B ⊗[A] T) :
    graphMul (χ.comp φ) (map (AlgHom.id A B) χ x) = χ (graphMul φ x) := by
  induction x with
  | tmul b t => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Graph idempotents are natural in the target. -/
theorem map (he : IsGraphIdempotent φ e) {T' : Type w'} [CommRing T'] [Algebra A T']
    (χ : T →ₐ[A] T') :
    IsGraphIdempotent (χ.comp φ) (Algebra.TensorProduct.map (AlgHom.id A B) χ e) where
  isIdempotentElem := he.isIdempotentElem.map _
  graphMul_eq_one := by rw [graphMul_map, he.graphMul_eq_one, map_one]
  tmul_one_mul b := by
    have h := congrArg (Algebra.TensorProduct.map (AlgHom.id A B) χ) (he.tmul_one_mul b)
    rw [map_mul, map_mul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgHom.id_apply, map_one] at h
    rw [AlgHom.comp_apply]
    exact h

/-- A graph idempotent is minimal among idempotents that stay nonzero after every base
change to a nonzero ring. -/
theorem eq_of_le (he : IsGraphIdempotent φ e) (hf : IsIdempotentElem f) (hle : f * e = f)
    (hne : ∀ (T₂ : Type w) [CommRing T₂] [Algebra A T₂] (χ : T →ₐ[A] T₂), Nontrivial T₂ →
      Algebra.TensorProduct.map (AlgHom.id A B) χ f ≠ 0) : f = e := by
  have hfe := he.eq_mul_of_mul_eq hle
  set s := graphMul φ f with hs
  have hsi : IsIdempotentElem s := hf.map _
  by_cases h1 : s = 1
  · rw [hfe, h1, ← one_def, mul_one]
  · exfalso
    have hJ := span_ne_top_of_ne_one hsi h1
    have : Nontrivial (T ⧸ Ideal.span {s}) := Ideal.Quotient.nontrivial_iff.mpr hJ
    apply hne (T ⧸ Ideal.span {s}) (Ideal.Quotient.mkₐ A (Ideal.span {s})) this
    rw [hfe, map_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self s),
      tmul_zero, mul_zero]

end IsGraphIdempotent

end Basic

section Existence

/-- The diagonal idempotent of an unramified algebra. -/
theorem exists_isGraphIdempotent_id [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] :
    ∃ δ : B ⊗[A] B, IsGraphIdempotent (AlgHom.id A B) δ := by
  obtain ⟨e, he, hsp⟩ : ∃ e, IsIdempotentElem e ∧
      KaehlerDifferential.ideal A B = Submodule.span (B ⊗[A] B) {e} :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg A B)).mp <|
      (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton Ω[B⁄A]
  have hmul : ∀ x : B ⊗[A] B, graphMul (AlgHom.id A B) x = Algebra.TensorProduct.lmul' A x := by
    intro x
    induction x with
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have he0 : graphMul (AlgHom.id A B) e = 0 := by
    rw [hmul]
    have : e ∈ KaehlerDifferential.ideal A B := by
      rw [hsp]; exact Submodule.mem_span_singleton_self e
    exact this
  refine ⟨1 - e, he.one_sub, ?_, ?_⟩
  · rw [map_sub, map_one, he0, sub_zero]
  · intro b
    have hx := KaehlerDifferential.one_smul_sub_smul_one_mem_ideal A b
    rw [hsp, Submodule.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    rw [smul_eq_mul] at hc
    have he' : e * e = e := he.eq
    rw [AlgHom.id_apply]
    linear_combination (1 - e) * hc + c * he'

variable {T : Type w} [CommRing T] [Algebra A T]

/-- Every algebra map out of an unramified algebra has a graph idempotent. -/
theorem exists_isGraphIdempotent [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B]
    (φ : B →ₐ[A] T) : ∃ e : B ⊗[A] T, IsGraphIdempotent φ e := by
  obtain ⟨δ, hδ⟩ := exists_isGraphIdempotent_id (A := A) (B := B)
  have h := hδ.map φ
  rw [AlgHom.comp_id] at h
  exact ⟨_, h⟩

end Existence

section DualBasis

/-- A finite projective module has a finite dual basis. -/
theorem exists_dualBasis [Module.Finite A B] [Module.Projective A B] :
    ∃ (n : ℕ) (v : Fin n → B) (c : Fin n → B →ₗ[A] A), ∀ b, ∑ i, c i b • v i = b := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A B
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨n, fun i => f (fun j => if i = j then 1 else 0), fun i => (LinearMap.proj i).comp h,
    fun b => ?_⟩
  have hb : f (h b) = b := LinearMap.congr_fun hh b
  rw [LinearMap.pi_apply_eq_sum_univ f (h b)] at hb
  simpa using hb

variable {T : Type w} [CommRing T] [Algebra A T]

/-- The `T`-linear coordinate `b ⊗ t ↦ c b • t` on `B ⊗_A T`. -/
def coordTensor (c : B →ₗ[A] A) : B ⊗[A] T →ₗ[A] T :=
  (TensorProduct.lid A T).toLinearMap ∘ₗ LinearMap.rTensor T c

@[simp] theorem coordTensor_tmul (c : B →ₗ[A] A) (b : B) (t : T) :
    coordTensor c (b ⊗ₜ[A] t) = c b • t := by
  simp [coordTensor]

theorem coordTensor_one_tmul_mul (c : B →ₗ[A] A) (t : T) (x : B ⊗[A] T) :
    coordTensor c (((1 : B) ⊗ₜ[A] t) * x) = t * coordTensor c x := by
  induction x with
  | tmul b t' => rw [tmul_mul_tmul, one_mul, coordTensor_tmul, coordTensor_tmul, mul_smul_comm]
  | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, mul_add]

theorem coordTensor_map {T' : Type w'} [CommRing T'] [Algebra A T'] (c : B →ₗ[A] A)
    (χ : T →ₐ[A] T') (x : B ⊗[A] T) :
    coordTensor c (Algebra.TensorProduct.map (AlgHom.id A B) χ x) = χ (coordTensor c x) := by
  induction x with
  | tmul b t => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sum_tmul_coordTensor {n : ℕ} {v : Fin n → B} {c : Fin n → B →ₗ[A] A}
    (hv : ∀ b, ∑ i, c i b • v i = b) (x : B ⊗[A] T) :
    ∑ i, (v i ⊗ₜ[A] (1 : T)) * ((1 : B) ⊗ₜ[A] coordTensor (c i) x) = x := by
  induction x with
  | tmul b t =>
    calc ∑ i, (v i ⊗ₜ[A] (1 : T)) * ((1 : B) ⊗ₜ[A] coordTensor (c i) (b ⊗ₜ[A] t))
        = ∑ i, (c i b • v i) ⊗ₜ[A] t := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [tmul_mul_tmul, mul_one, one_mul, coordTensor_tmul, TensorProduct.tmul_smul,
            TensorProduct.smul_tmul']
      _ = b ⊗ₜ[A] t := by rw [← TensorProduct.sum_tmul, hv b]
  | add x y hx hy =>
    simp_rw [map_add, tmul_add, mul_add, Finset.sum_add_distrib, hx, hy]

end DualBasis

end General

section Converse

variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T] [Algebra A B]
  [Algebra A T]

/-- An idempotent `e` of `B ⊗_A T` is a graph idempotent as soon as (1) over
`D = (B ⊗_A T)/(1 - e)`, the image `e_D` of `e` is minimal among idempotents that stay
nonzero after every base change to a nonzero ring, and (2) the image of `e` in `B ⊗_A κ`
is nonzero for every residue field `κ = T/m` of `T`. -/
theorem exists_isGraphIdempotent_of_minimal [Module.Finite A B] [Module.Projective A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B]
    {e : B ⊗[A] T} (he : IsIdempotentElem e)
    (hmin : ∀ f : B ⊗[A] (B ⊗[A] T ⧸ Ideal.span {1 - e}), IsIdempotentElem f →
      f * Algebra.TensorProduct.map (AlgHom.id A B)
        ((Ideal.Quotient.mkₐ A (Ideal.span {1 - e})).comp includeRight) e = f →
      (∀ (T₂ : Type u) [CommRing T₂] [Algebra A T₂]
        (χ : (B ⊗[A] T ⧸ Ideal.span {1 - e}) →ₐ[A] T₂), Nontrivial T₂ →
          Algebra.TensorProduct.map (AlgHom.id A B) χ f ≠ 0) →
      f = Algebra.TensorProduct.map (AlgHom.id A B)
          ((Ideal.Quotient.mkₐ A (Ideal.span {1 - e})).comp includeRight) e)
    (hne : ∀ m : Ideal T, m.IsMaximal →
      Algebra.TensorProduct.map (AlgHom.id A B) (Ideal.Quotient.mkₐ A m) e ≠ 0) :
    ∃ φ : B →ₐ[A] T, IsGraphIdempotent φ e := by
  set I : Ideal (B ⊗[A] T) := Ideal.span {1 - e} with hI
  set q : B ⊗[A] T →ₐ[A] (B ⊗[A] T ⧸ I) := Ideal.Quotient.mkₐ A I with hq
  set j : T →ₐ[A] (B ⊗[A] T ⧸ I) := q.comp includeRight with hj
  set π : B →ₐ[A] (B ⊗[A] T ⧸ I) := q.comp includeLeft with hπdef
  have hqe : q e = 1 := by
    have h0 : q (1 - e) = 0 := by
      rw [hq, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0.symm
  have hqmul : ∀ x, q (x * e) = q x := fun x => by rw [map_mul, hqe, mul_one]
  have hqtmul : ∀ b t, q (b ⊗ₜ[A] t) = π b * j t := by
    intro b t
    rw [hπdef, hj, AlgHom.comp_apply, AlgHom.comp_apply, includeLeft_apply, includeRight_apply,
      ← map_mul, tmul_mul_tmul, mul_one, one_mul]
  have hgm : ∀ x, graphMul π (Algebra.TensorProduct.map (AlgHom.id A B) j x) = q x := by
    intro x
    induction x with
    | tmul b t =>
      rw [Algebra.TensorProduct.map_tmul, productMap_apply_tmul, AlgHom.id_apply, AlgHom.id_apply]
      exact (hqtmul b t).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨eπ, hπ⟩ := exists_isGraphIdempotent π
  set eD := Algebra.TensorProduct.map (AlgHom.id A B) j e with heD
  have hD1 : graphMul π eD = 1 := by rw [heD, hgm, hqe]
  have hle : eπ * eD = eπ := by
    have h := hπ.mul_eq (1 - eD)
    rw [map_sub, map_one, hD1, sub_self, tmul_zero, zero_mul, sub_mul, one_mul,
      sub_eq_zero] at h
    rw [mul_comm]; exact h.symm
  have hfs : eπ = eD := hmin eπ hπ.isIdempotentElem hle fun T₂ _ _ χ _ => (hπ.map χ).ne_zero
  have hgraphD : IsGraphIdempotent π eD := hfs ▸ hπ
  -- dual basis
  obtain ⟨n, v, c, hv⟩ := exists_dualBasis (A := A) (B := B)
  -- the coordinates of `e` generate the unit ideal
  have hU : ∃ a : Fin n → T, ∑ i, a i * coordTensor (c i) e = 1 := by
    by_contra hcon
    have hJ : Ideal.span (Set.range fun i => coordTensor (c i) e) ≠ ⊤ := by
      intro htop
      apply hcon
      rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at htop
      exact htop
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ hJ
    apply hne m hm
    conv_lhs => rw [← sum_tmul_coordTensor hv e]
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hmem : coordTensor (c i) e ∈ m := hJm (Ideal.subset_span ⟨i, rfl⟩)
    rw [map_mul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      Ideal.Quotient.mkₐ_eq_mk, (Ideal.Quotient.eq_zero_iff_mem).mpr hmem, tmul_zero, mul_zero]
  obtain ⟨a, ha⟩ := hU
  -- the key identity
  have hE : ∀ i x, j (coordTensor (c i) (x * e)) = q x * j (coordTensor (c i) e) := by
    intro i x
    induction x with
    | tmul b t =>
      have h1 : (b ⊗ₜ[A] t) * e = ((1 : B) ⊗ₜ[A] t) * ((b ⊗ₜ[A] (1 : T)) * e) := by
        rw [← mul_assoc, tmul_mul_tmul, one_mul, mul_one]
      have h2 := congrArg (coordTensor (T := B ⊗[A] T ⧸ I) (c i)) (hgraphD.tmul_one_mul b)
      have h3 : (b ⊗ₜ[A] (1 : B ⊗[A] T ⧸ I)) * eD =
          Algebra.TensorProduct.map (AlgHom.id A B) j ((b ⊗ₜ[A] (1 : T)) * e) := by
        rw [heD, map_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
      rw [h3, coordTensor_map, coordTensor_one_tmul_mul, heD, coordTensor_map] at h2
      rw [h1, coordTensor_one_tmul_mul, map_mul, h2, hqtmul]
      ring
    | add x y hx hy => rw [add_mul, map_add, map_add, hx, hy, map_add, add_mul]
  have hsurj : Function.Surjective j := by
    intro d
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective A I d
    refine ⟨∑ i, a i * coordTensor (c i) (x * e), ?_⟩
    rw [map_sum]
    calc ∑ i, j (a i * coordTensor (c i) (x * e))
        = ∑ i, q x * j (a i * coordTensor (c i) e) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul j, map_mul j, hE]; ring
      _ = q x * j (∑ i, a i * coordTensor (c i) e) := by rw [map_sum, Finset.mul_sum]
      _ = q x := by rw [ha, map_one, mul_one]
  have hinj : Function.Injective j := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    have hmem : ((1 : B) ⊗ₜ[A] t) ∈ I := by
      rw [hj, AlgHom.comp_apply, includeRight_apply, hq, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem] at ht
      exact ht
    have h0 := mul_eq_zero_of_mem_span he hmem
    calc t = t * ∑ i, a i * coordTensor (c i) e := by rw [ha, mul_one]
      _ = ∑ i, a i * coordTensor (c i) (((1 : B) ⊗ₜ[A] t) * e) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [coordTensor_one_tmul_mul]; ring
      _ = 0 := by simp [h0]
  let jeq := AlgEquiv.ofBijective j ⟨hinj, hsurj⟩
  let φ : B →ₐ[A] T := (jeq.symm : (B ⊗[A] T ⧸ I) →ₐ[A] T).comp π
  have hjφ : ∀ b, j (φ b) = π b := fun b => jeq.apply_symm_apply (π b)
  have hjgm : ∀ x, j (graphMul φ x) = q x := by
    intro x
    induction x with
    | tmul b t => rw [productMap_apply_tmul, AlgHom.id_apply, map_mul, hjφ, hqtmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨φ, he, ?_, ?_⟩
  · apply hinj
    rw [hjgm, hqe, map_one]
  · intro b
    have hy : ((b ⊗ₜ[A] (1 : T)) - ((1 : B) ⊗ₜ[A] φ b)) * e ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk A]
      change q _ = 0
      rw [hqmul, map_sub, hqtmul, hqtmul, map_one, map_one, mul_one, one_mul, hjφ, sub_self]
    have h0 := mul_eq_zero_of_mem_span he hy
    rw [mul_assoc, he.eq, sub_mul, sub_eq_zero] at h0
    exact h0

end Converse

end Langlands.Algebra.GraphIdempotent
