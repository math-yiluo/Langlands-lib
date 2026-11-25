/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
public import WeilConjectures.Evaluation
public import WeilConjectures.Mathlib.Analysis.Normed.Field.Basic
public import WeilConjectures.NumberTheory.Padics.Logarithm
public import WeilConjectures.PointCount
public import WeilConjectures.RepresentationTheory.IntegralModel

/-!
# Rank-one Weil characters on a curve

Let `W` be the Weil group of a smooth geometrically connected curve `C₀` over `𝔽_q`, linked to
the étale fundamental group (`AlgebraicGeometry.WeilGroup.IsEtaleQuotient`), and `ℓ ≠ p`. This
file proves that a continuous character `χ : W → ℚ̄_ℓˣ` has finite geometric image, and hence
that the rank-one Weil sheaf it defines is punctually `ι`-pure of weight
`2 log_q |ι (χ γ)|` (blueprint subsection `theorem-rank-one-sheaves-have-finite`).

The proof of finiteness follows the blueprint. The values of `χ` on `π₁(C)` lie in a finite
extension `E / ℚ_ℓ` (`proposition-lattices-representations-normal-scheme`); some power `χ ^ N` takes
values in `1 + ℓ² 𝒪_E`, on which the logarithm is an injective homomorphism
(`theorem-rank-one-sheaves-have-finite`). The coordinates of `log ∘ χ ^ N` in a `ℚ_ℓ`-basis of `E`
are continuous homomorphisms `π₁(C) → ℚ_ℓ` invariant under conjugation by the Frobenius lift, hence
zero (`AlgebraicGeometry.WeilGroup.eq_one_of_conj_invariant`).

## Main statements

- `AlgebraicGeometry.WeilGroup.exists_pow_eq_one_of_continuous` and
  `AlgebraicGeometry.WeilGroup.finite_range_of_continuous`: finite geometric image.
- `AlgebraicGeometry.WeilGroup.frobeniusWeight_eq_of_continuous`: the local weights of a
  continuous character.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]

namespace WeilGroup

/-- Blueprint `corollary-rank-one-weights`: Modulus of a root of unity.

A root of unity has weight `0` for every `ι` and every residue cardinality. -/
theorem frobeniusWeight_eq_zero_of_pow_eq_one {E : Type*} [Field E] (ι : E →+* ℂ) (qx : ℕ)
    {ζ : E} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) : frobeniusWeight ι qx ζ = 0 := by
  rw [frobeniusWeight, norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ, map_one]) hn,
    Real.log_one, mul_zero, zero_div]

variable (W : WeilGroup p) {l : ℕ} [Fact l.Prime]

section RankOne

variable [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] [Fact (ringChar K ≠ l)]
  [W.IsEtaleQuotient]

/-- The `ℚ_ℓ`-valued form of `AlgebraicGeometry.WeilGroup.eq_one_of_conj_invariant`: a
continuous homomorphism `π₁(C) → ℚ_ℓ` invariant under conjugation by the Frobenius lift is
trivial. Its image is compact, hence bounded, so a multiple `ℓ ^ a b` takes values in `ℤ_ℓ`. -/
theorem eq_one_of_conj_invariant_of_continuous (b : W.geometric →* Multiplicative ℚ_[l])
    (hcont : Continuous b)
    (hb : ∀ g h : W.geometric, (h : W.carrier) = W.frobeniusLift⁻¹ * g * W.frobeniusLift →
      b h = b g) :
    b = 1 := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  let f : W.geometric → ℚ_[l] := fun g ↦ (b g).toAdd
  have hf : Continuous f := continuous_toAdd.comp hcont
  obtain ⟨M, hM⟩ := (isCompact_range hf).isBounded.exists_norm_le
  obtain ⟨a, ha⟩ := pow_unbounded_of_one_lt M hl
  have hnorm (g : W.geometric) : ‖(l : ℚ_[l]) ^ a * f g‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast]
    rw [inv_mul_le_iff₀ (pow_pos (zero_lt_one.trans hl) a), mul_one]
    exact (hM _ ⟨g, rfl⟩).trans ha.le
  let b' : W.geometric →ₜ* Multiplicative ℤ_[l] :=
    { toFun g := .ofAdd ⟨(l : ℚ_[l]) ^ a * f g, hnorm g⟩
      map_one' := by
        apply Multiplicative.toAdd.injective
        refine Subtype.ext ?_
        simp [f]
      map_mul' g h := by
        apply Multiplicative.toAdd.injective
        refine Subtype.ext ?_
        simp [f, mul_add]
      continuous_toFun := continuous_ofAdd.comp
        ((continuous_const.mul hf).subtype_mk hnorm) }
  have h1 := W.eq_one_of_conj_invariant b' fun g h hgh ↦ by
    have hfgh : f h = f g := congrArg Multiplicative.toAdd (hb g h hgh)
    apply Multiplicative.toAdd.injective
    refine Subtype.ext ?_
    change (l : ℚ_[l]) ^ a * f h = (l : ℚ_[l]) ^ a * f g
    rw [hfgh]
  ext g
  have h2 : (l : ℚ_[l]) ^ a * f g = 0 := congrArg (fun φ ↦ ((φ g).toAdd : ℚ_[l])) h1
  have h3 : f g = 0 := (mul_eq_zero.mp h2).resolve_left
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero))
  exact Multiplicative.toAdd.injective h3

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: Finite geometric image of a
rank-one Weil character on a curve.

A continuous character `χ : W(C₀) → ℚ̄_ℓˣ` has finite geometric image: there is `N ≥ 1` with
`χ (g) ^ N = 1` for every `g ∈ π₁(C)`. -/
theorem exists_pow_eq_one_of_continuous (χ : W.carrier →* (PadicAlgCl l)ˣ)
    (hχ : Continuous fun g : W.geometric ↦ (χ g : PadicAlgCl l)) :
    ∃ N : ℕ, 0 < N ∧ ∀ g : W.geometric, χ g ^ N = 1 := by
  classical
  -- the values of `χ` on `π₁(C)` lie in a finite extension `E` of `ℚ_ℓ`
  let φ : W.geometric →* Matrix (Fin 1) (Fin 1) (PadicAlgCl l) :=
    (Matrix.scalar (Fin 1) : PadicAlgCl l →+* _).toMonoidHom.comp
      ((Units.coeHom _).comp (χ.comp W.geometric.subtype))
  have hφ (i j : Fin 1) : Continuous fun g ↦ φ g i j := by
    simpa [φ, Subsingleton.elim i j] using hχ
  obtain ⟨E, hE, hmem⟩ := PadicAlgCl.exists_finiteDimensional_forall_mem l φ hφ
  have hχE (g : W.geometric) : (χ g : PadicAlgCl l) ∈ E := by simpa [φ] using hmem g 0 0
  let ψ₀ : W.geometric →* E :=
    { toFun g := ⟨χ g, hχE g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' g h := Subtype.ext (by simp) }
  let ψ : W.geometric →* Eˣ := ψ₀.toHomUnits
  have hψ (g : W.geometric) : (((ψ g : E)) : PadicAlgCl l) = χ g := rfl
  -- some power of `ψ` takes values in `U_E = 1 + ℓ² 𝒪_E`
  let H : Subgroup W.geometric := (PadicAlgCl.smallUnits l E).comap ψ
  have hmemH (g : W.geometric) : g ∈ H ↔
      ‖(χ g : PadicAlgCl l) - 1‖ ≤ ‖(l : PadicAlgCl l)‖ ^ 2 := by
    have hl0 : 0 < ‖(l : PadicAlgCl l)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr
      (Fact.out : l.Prime).ne_zero)
    rw [Subgroup.mem_comap]
    change (((ψ g : E) - 1) / ((l : E) ^ 2)) ∈ PadicAlgCl.integers l E ↔ _
    rw [PadicAlgCl.mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm, map_div₀, map_sub, map_one,
      map_pow, map_natCast, IntermediateField.algebraMap_apply, hψ, norm_div, norm_pow,
      NNReal.coe_one, div_le_one (pow_pos hl0 2)]
  have hHopen : IsOpen (H : Set W.geometric) := by
    have hball : (H : Set W.geometric) = (fun g : W.geometric ↦ (χ g : PadicAlgCl l)) ⁻¹'
        Metric.closedBall 1 (‖(l : PadicAlgCl l)‖ ^ 2) := by
      ext g
      rw [SetLike.mem_coe, hmemH, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    rw [hball]
    refine (IsUltrametricDist.isOpen_closedBall _ ?_).preimage hχ
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (Nat.cast_ne_zero.mpr
      (Fact.out : l.Prime).ne_zero))
  have : H.Normal := Subgroup.normal_comap ψ
  have : Finite (W.geometric ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHopen
  set N := H.index with hN
  have hN0 : N ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hpow (g : W.geometric) : ψ g ^ N ∈ PadicAlgCl.smallUnits l E := by
    have := H.pow_index_mem g
    rwa [Subgroup.mem_comap, map_pow] at this
  let u : W.geometric →* PadicAlgCl.smallUnits l E :=
    ((powMonoidHom N).comp ψ).codRestrict _ hpow
  have hu (g : W.geometric) :
      ((((u g : Eˣ) : E)) : PadicAlgCl l) = (χ g : PadicAlgCl l) ^ N := by
    change ((((ψ g) ^ N : Eˣ) : E) : PadicAlgCl l) = _
    rw [Units.val_pow_eq_pow_val, IntermediateField.coe_pow, hψ]
  have hlog0 : PadicAlgCl.smallLog l E 0 = 0 := by simp [PadicAlgCl.smallLog]
  -- the logarithm of `u`
  let lam (g : W.geometric) : E := PadicAlgCl.smallLog l E (((u g : Eˣ) : E) - 1)
  have hlam_one : lam 1 = 0 := by
    simp only [lam, map_one, OneMemClass.coe_one, Units.val_one, sub_self, hlog0]
  have hlam_mul (g h : W.geometric) : lam (g * h) = lam g + lam h := by
    simp only [lam, map_mul]
    exact PadicAlgCl.smallLog_mul l E (u g) (u h)
  have hlam_norm (g : W.geometric) : ‖lam g‖ ≤ ‖(χ g : PadicAlgCl l) ^ N - 1‖ := by
    have h := PadicAlgCl.norm_smallLog_le l E (u g).2
    rwa [map_sub, map_one, IntermediateField.algebraMap_apply,
      IntermediateField.algebraMap_apply, hu] at h
  have hlam_conj (g h : W.geometric)
      (hgh : (h : W.carrier) = W.frobeniusLift⁻¹ * g * W.frobeniusLift) : lam h = lam g := by
    have : χ h = χ g := by
      rw [hgh, map_mul, map_mul, mul_comm, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one,
        one_mul]
    have hu : u h = u g := Subtype.ext (Units.ext (Subtype.ext (by simp [u, ψ, ψ₀, this])))
    simp only [lam, hu]
  -- its coordinates vanish
  have hcoord (t : E →ₗ[ℚ_[l]] ℚ_[l]) (g : W.geometric) : t (lam g) = 0 := by
    let b : W.geometric →* Multiplicative ℚ_[l] :=
      { toFun g := .ofAdd (t (lam g))
        map_one' := by simp [hlam_one]
        map_mul' g h := by simp [hlam_mul, ofAdd_add] }
    have ht : Continuous t := LinearMap.continuous_of_finiteDimensional t
    have hb : Continuous b := by
      refine continuous_of_continuousAt_one b ?_
      rw [ContinuousAt, map_one, Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.mp ht 0 ε hε
      have hχN : Filter.Tendsto (fun g : W.geometric ↦ (χ g : PadicAlgCl l) ^ N - 1)
          (nhds 1) (nhds 0) := by
        have h : Continuous fun g : W.geometric ↦ (χ g : PadicAlgCl l) ^ N - 1 :=
          (hχ.pow N).sub continuous_const
        simpa using h.tendsto 1
      filter_upwards [Metric.tendsto_nhds.mp hχN δ hδ] with g hg
      have h1 : dist (lam g) 0 < δ := by
        rw [dist_zero_right]
        rw [dist_zero_right] at hg
        exact (hlam_norm g).trans_lt hg
      have h2 := hδε (lam g) h1
      rw [map_zero] at h2
      exact h2
    have h1 := W.eq_one_of_conj_invariant_of_continuous b hb fun g h hgh ↦ by
      simp [b, hlam_conj g h hgh]
    exact congrArg (fun φ ↦ (φ g).toAdd) h1
  refine ⟨N, Nat.pos_of_ne_zero hN0, fun g ↦ ?_⟩
  have hlam0 : lam g = 0 := by
    let B := Module.finBasis ℚ_[l] E
    refine B.ext_elem fun i ↦ ?_
    simpa using hcoord (B.coord i) g
  have hu1 : u g = 1 := by
    refine Subtype.ext (PadicAlgCl.injOn_smallLog l E (u g).2 (one_mem _) ?_)
    change lam g = PadicAlgCl.smallLog l E (((1 : Eˣ) : E) - 1)
    rw [Units.val_one, sub_self, hlog0, hlam0]
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, ← hu g, hu1]
  rfl

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: Finite geometric image of a
rank-one Weil character on a curve.

A continuous character `χ : W(C₀) → ℚ̄_ℓˣ` takes finitely many values on `π₁(C)`. -/
theorem finite_range_of_continuous (χ : W.carrier →* (PadicAlgCl l)ˣ)
    (hχ : Continuous fun g : W.geometric ↦ (χ g : PadicAlgCl l)) :
    (Set.range fun g : W.geometric ↦ χ g).Finite := by
  obtain ⟨N, hN, h⟩ := W.exists_pow_eq_one_of_continuous χ hχ
  have : NeZero N := ⟨hN.ne'⟩
  refine (Set.finite_range ((↑) : rootsOfUnity N (PadicAlgCl l) → (PadicAlgCl l)ˣ)).subset ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨⟨χ g, (mem_rootsOfUnity _ _).mpr (h g)⟩, rfl⟩

/-- Blueprint `corollary-rank-one-weights--1`: Punctual purity of a rank-one Weil
character on a curve.

A continuous character `χ` of the Weil group is punctually `ι`-pure of weight
`w = 2 log |ι (χ γ)| / log q`, for the Frobenius lift `γ`: at a closed point `x` of degree `d`,
`χ (F_x) = χ (F_x γ⁻ᵈ) χ (γ) ^ d` with `χ (F_x γ⁻ᵈ)` a root of unity, so that
`|ι χ (F_x)| = |ι (χ γ)| ^ d` and `q_x = q ^ d`. -/
theorem frobeniusWeight_eq_of_continuous (χ : W.carrier →* (PadicAlgCl l)ˣ)
    (hχ : Continuous fun g : W.geometric ↦ (χ g : PadicAlgCl l)) (ι : PadicAlgCl l →+* ℂ)
    (x : C.finitePoints) :
    frobeniusWeight ι (C.pointNorm x.1) (χ (W.frobenius x)) =
      frobeniusWeight ι (Nat.card K) (χ W.frobeniusLift) := by
  obtain ⟨N, hN, hpow⟩ := W.exists_pow_eq_one_of_continuous χ hχ
  set d := p.degreeOver x.1
  have hd : d ≠ 0 := p.degreeOver_ne_zero x.2
  have hg : W.frobenius x * W.frobeniusLift ^ (-(d : ℤ)) ∈ W.geometric := by
    rw [MonoidHom.mem_ker, map_mul, map_zpow, W.deg_frobenius, W.deg_frobeniusLift,
      ← ofAdd_zsmul, ← ofAdd_add, smul_eq_mul, mul_one, add_neg_cancel, ofAdd_zero]
  have hFx : χ (W.frobenius x) = χ (⟨_, hg⟩ : W.geometric) * χ W.frobeniusLift ^ d := by
    rw [Subgroup.coe_mk, map_mul, map_zpow, mul_assoc, ← zpow_natCast, ← zpow_add,
      neg_add_cancel, zpow_zero, mul_one]
  have hgn : ‖ι (χ (⟨_, hg⟩ : W.geometric))‖ = 1 := by
    refine norm_eq_one_of_pow_eq_one ?_ hN.ne'
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hpow, Units.val_one, map_one]
  have hq : (1 : ℝ) < Nat.card K := by exact_mod_cast Finite.one_lt_card
  have hlogq : Real.log (Nat.card K) ≠ 0 := (Real.log_pos hq).ne'
  rw [frobeniusWeight, frobeniusWeight, hFx, Units.val_mul, Units.val_pow_eq_pow_val, map_mul,
    map_pow, norm_mul, norm_pow, hgn, one_mul, Real.log_pow,
    p.pointNorm_eq_pow_degreeOver x.2, Nat.cast_pow, Real.log_pow]
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  field_simp
  exact mul_div_cancel_left₀ _ hd'

/-- Blueprint `corollary-rank-one-weights--1`: Punctual purity of a rank-one Weil
character on a curve.

The weight `2 log |ι (χ s)| / log q` does not depend on the choice of the element `s` of degree
one: two such elements differ by an element of `π₁(C)`, on which `χ` takes root of unity
values. -/
theorem frobeniusWeight_eq_of_deg_eq_one (χ : W.carrier →* (PadicAlgCl l)ˣ)
    (hχ : Continuous fun g : W.geometric ↦ (χ g : PadicAlgCl l)) (ι : PadicAlgCl l →+* ℂ)
    {s : W.carrier} (hs : W.deg s = Multiplicative.ofAdd 1) :
    frobeniusWeight ι (Nat.card K) (χ s) = frobeniusWeight ι (Nat.card K) (χ W.frobeniusLift) := by
  obtain ⟨N, hN, hpow⟩ := W.exists_pow_eq_one_of_continuous χ hχ
  have hg : s * W.frobeniusLift⁻¹ ∈ W.geometric := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs, W.deg_frobeniusLift, mul_inv_cancel]
  have hs' : χ s = χ (⟨_, hg⟩ : W.geometric) * χ W.frobeniusLift := by
    rw [Subgroup.coe_mk, map_mul, map_inv, inv_mul_cancel_right]
  have hgn : ‖ι (χ (⟨_, hg⟩ : W.geometric))‖ = 1 := by
    refine norm_eq_one_of_pow_eq_one ?_ hN.ne'
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hpow, Units.val_one, map_one]
  rw [frobeniusWeight, frobeniusWeight, hs', Units.val_mul, map_mul, norm_mul, hgn, one_mul]

end RankOne

end WeilGroup

end AlgebraicGeometry
