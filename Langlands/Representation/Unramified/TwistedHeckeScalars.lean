import Langlands.Representation.Unramified.PairedHeckeScalars
import Langlands.Representation.Unramified.EigenvalueScaling

/-! # Standard Hecke scalars of character twists

If a smooth representation `σ` of `GL_(r+1)(F)` is the twist of `ρ` by a character `ψ`
that is trivial on `GL_(r+1)(O_F)` and takes the value `u ^ i` on the `i`-th standard
diagonal, then the standard Hecke scalars of `σ` are those of `ρ` multiplied by `u ^ i`,
so the spectrum of `σ` is the spectrum of `ρ` scaled by `u`.
-/

noncomputable section

namespace Langlands.Unramified

open Correspondence MinusculeCosets

universe uF uV uW

/-- The standard Hecke scalars determine the spectrum. -/
theorem eq_of_standardHeckeScalar_eq {p : ℕ} [Fact p.Prime] (K : PadicField.{uF} p) {r : ℕ}
    {s t : Eigenvalues (r + 1)}
    (h : ∀ i : Fin (r + 2), standardHeckeScalar K s i = standardHeckeScalar K t i) :
    s = t := by
  have hsq : (Real.sqrt (K.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) ≠ 0 := by
    have := K.canonicalTopologicalData.residueCardinality_gt_one
    have hq : (0 : ℝ) < K.canonicalTopologicalData.residueCardinality := by
      exact_mod_cast Nat.zero_lt_of_lt this
    exact_mod_cast (Real.sqrt_pos.2 hq).ne'
  have hcoeff : ∀ i : Fin (r + 2),
      elementaryCoefficient s i.val = elementaryCoefficient t i.val :=
    fun i => mul_left_cancel₀ (pow_ne_zero _ hsq) (h i)
  apply Eigenvalues.eulerPolynomial_injective
  ext n
  by_cases hn : n ≤ r + 1
  · have h := hcoeff ⟨n, by omega⟩
    exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (by rw [Eigenvalues.eulerPolynomial_natDegree]; omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by rw [Eigenvalues.eulerPolynomial_natDegree]; omega)]

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

namespace PairedHecke

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {r : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A character trivial on the spherical subgroup takes the same value on every labelled
representative of the `i`-th standard double coset as on the `i`-th standard diagonal. -/
theorem character_labelledRep (ψ : GeneralLinear (r + 1) F.Carrier →* ℂˣ)
    (hψ : ∀ k ∈ sphericalSubgroup F r, ψ k = 1) (i : Fin (r + 2))
    (α : CosetIndex F.canonicalTopologicalData.ResidueField (r + 1) i.val) :
    ψ (labelledRep F.canonicalTopologicalData.uniformizerUnit (residueLift F) α) =
      ψ (standardDiagonal F r i) := by
  obtain ⟨k₁, hk₁, k₂, hk₂, hx⟩ :=
    labelledRep_mem_doubleCoset (ϖ := F.canonicalTopologicalData.uniformizerUnit)
      (residueLift_mem F) (card_initialSegment r i) α
  rw [hx, map_mul, map_mul, hψ k₁ hk₁, hψ k₂ hk₂, one_mul, mul_one,
    ← standardDiagonal_eq_subsetTorus]

/-- If `σ` is the twist of `ρ` through `e` by a character `ψ` that is trivial on the
spherical subgroup and equals `u ^ i` on the `i`-th standard diagonal, and `ρ` and `σ`
have the standard Hecke scalars of `s` and `t` on all spherical vectors, then a nonzero
spherical vector of `ρ` forces `t` to be `s` scaled by `u`. -/
theorem eq_scale_of_twist (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W)
    (hσ : IsSmooth σ) (e : V ≃ₗ[ℂ] W) (ψ : GeneralLinear (r + 1) F.Carrier →* ℂˣ)
    (he : ∀ g x, σ g (e x) = (ψ g : ℂ) • e (ρ g x))
    (hψ : ∀ k ∈ sphericalSubgroup F r, ψ k = 1) (u : ℂˣ)
    (hu : ∀ i, ψ (standardDiagonal F r i) = u ^ i.val) (s t : Eigenvalues (r + 1))
    (hs : ∀ (a : fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup) (i : Fin (r + 2)),
      corner F ρ hρ (standardHeckeElement F r i) a = standardHeckeScalar F s i • a)
    (ht : ∀ (b : fixedVectors σ (sphericalOpenSubgroup F r).toSubgroup) (i : Fin (r + 2)),
      corner F σ hσ (standardHeckeElement F r i) b = standardHeckeScalar F t i • b)
    (a : fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup) (ha : a ≠ 0) :
    t = Eigenvalues.scale u s := by
  have hb : e (a : V) ∈ fixedVectors σ (sphericalOpenSubgroup F r).toSubgroup := fun k =>
    (he (k : GeneralLinear (r + 1) F.Carrier) (a : V)).trans (by
      rw [hψ k k.2, Units.val_one, one_smul]
      exact congrArg e (a.property k))
  let b : fixedVectors σ (sphericalOpenSubgroup F r).toSubgroup := ⟨e (a : V), hb⟩
  have hea : e (a : V) ≠ 0 := fun h0 =>
    ha (Subtype.ext (e.injective (h0.trans e.map_zero.symm)))
  apply eq_of_standardHeckeScalar_eq F
  intro i
  rw [standardHeckeScalar_scale]
  apply smul_left_injective ℂ hea
  have hsum : (corner F σ hσ (standardHeckeElement F r i) b : W) =
      (u : ℂ) ^ i.val • e (corner F ρ hρ (standardHeckeElement F r i) a : V) :=
    calc (corner F σ hσ (standardHeckeElement F r i) b : W)
        = ∑ α : CosetIndex F.canonicalTopologicalData.ResidueField (r + 1) i.val,
            σ (labelledRep F.canonicalTopologicalData.uniformizerUnit (residueLift F) α)
              (e (a : V)) :=
          standardHecke_cornerAction_eq_sum F σ hσ i b
      _ = ∑ α : CosetIndex F.canonicalTopologicalData.ResidueField (r + 1) i.val,
            (u : ℂ) ^ i.val • e (ρ (labelledRep F.canonicalTopologicalData.uniformizerUnit
              (residueLift F) α) (a : V)) :=
          Finset.sum_congr rfl fun α _ => by
            rw [he, character_labelledRep F ψ hψ i α, hu, Units.val_pow_eq_pow_val]
      _ = (u : ℂ) ^ i.val • e (∑ α : CosetIndex F.canonicalTopologicalData.ResidueField
            (r + 1) i.val, ρ (labelledRep F.canonicalTopologicalData.uniformizerUnit
              (residueLift F) α) (a : V)) := by
          rw [map_sum, Finset.smul_sum]
      _ = (u : ℂ) ^ i.val • e (corner F ρ hρ (standardHeckeElement F r i) a : V) :=
          congrArg (fun y : V => (u : ℂ) ^ i.val • e y)
            (standardHecke_cornerAction_eq_sum F ρ hρ i a).symm
  calc standardHeckeScalar F t i • e (a : V)
      = (corner F σ hσ (standardHeckeElement F r i) b : W) :=
        (congrArg Subtype.val (ht b i)).symm
    _ = (u : ℂ) ^ i.val • e (corner F ρ hρ (standardHeckeElement F r i) a : V) := hsum
    _ = (u : ℂ) ^ i.val • e (standardHeckeScalar F s i • (a : V)) :=
        congrArg (fun y : fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup =>
          (u : ℂ) ^ i.val • e (y : V)) (hs a i)
    _ = ((u : ℂ) ^ i.val * standardHeckeScalar F s i) • e (a : V) := by
        rw [map_smul, smul_smul]

end PairedHecke

end Langlands.Unramified
