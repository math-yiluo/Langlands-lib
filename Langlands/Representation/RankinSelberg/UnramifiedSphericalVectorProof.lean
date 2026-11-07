import Langlands.Representation.RankinSelberg.UnramifiedPairStatement
import Langlands.Representation.RankinSelberg.UnramifiedWhittakerCells
import Langlands.Representation.RankinSelberg.UnramifiedRecursionUniqueness
import Langlands.Representation.Unramified.StandardHeckeSum
import Langlands.Representation.Unramified.SphericalFixedLineProof

/-!
# Normalized spherical Whittaker vectors

Jacquet–Shalika, *Euler products II*, §1.3: in every Whittaker model of an irreducible
admissible generic representation of `GL_(r+1)(F)` with a nonzero `GL_(r+1)(O)`-fixed
vector, for an additive character of conductor `O`, a nonzero right
`GL_(r+1)(O)`-invariant function does not vanish at the identity. Hence the model
contains exactly one normalized spherical vector.
-/

noncomputable section

namespace Langlands.RankinSelberg.UnramifiedWhittaker

open Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa Langlands.Conductor
open Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.Unramified Langlands.Unramified.MinusculeCosets Langlands.Correspondence
open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit transvection_apply)

universe uF uV

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-! ### Scalar matrices -/

/-- The scalar torus element `ϖ ^ c` (all exponents equal) is central. -/
theorem torus_const_commute {m : ℕ} (ϖ : F.Carrierˣ) (c : ℤ)
    (g : Langlands.GeneralLinear m F.Carrier) :
    torus ϖ (fun _ : Fin m => c) * g = g * torus ϖ (fun _ : Fin m => c) := by
  apply Units.ext
  ext a b
  rw [Units.val_mul, Units.val_mul, torus_val, Matrix.diagonal_mul, Matrix.mul_diagonal,
    mul_comm]

/-! ### Hecke scalars on a fixed line -/

section Line

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)

/-- On a one-dimensional fixed space, the sum of translates by the labelled coset
representatives of a standard double coset acts by a scalar. -/
theorem exists_labelledRep_sum_eq_smul (hρ : IsSmooth ρ)
    (v : fixedVectors ρ (sphericalSubgroup F r))
    (hline : ∀ w : fixedVectors ρ (sphericalSubgroup F r), ∃ c : ℂ, c • v = w)
    (i : Fin (r + 2)) :
    ∃ c : ℂ, ∑ α : CosetIndex F.canonicalTopologicalData.ResidueField (r + 1) i.val,
        ρ (labelledRep F.canonicalTopologicalData.uniformizerUnit (residueLift F) α) v =
      c • (v : V) := by
  obtain ⟨c, hc⟩ := hline
    (Hecke.cornerAction (sphericalHaar F r) ρ hρ (sphericalOpenSubgroup F r)
      (sphericalOpenSubgroup_isCompact F r) (standardHeckeElement F r i) v)
  refine ⟨c, ?_⟩
  rw [← standardHecke_cornerAction_eq_sum F ρ hρ i v, ← hc]
  rfl

/-- On a one-dimensional fixed space, a group element commuting with the spherical
subgroup acts by a scalar. -/
theorem exists_central_smul
    (v : fixedVectors ρ (sphericalSubgroup F r))
    (hline : ∀ w : fixedVectors ρ (sphericalSubgroup F r), ∃ c : ℂ, c • v = w)
    (z : Langlands.GeneralLinear (r + 1) F.Carrier) (hz : ∀ g, z * g = g * z) :
    ∃ c : ℂ, ρ z v = c • (v : V) := by
  have hmem : ρ z v ∈ fixedVectors ρ (sphericalSubgroup F r) := by
    intro k
    change ρ k (ρ z v) = ρ z v
    rw [← Module.End.mul_apply, ← map_mul, ← hz, map_mul, Module.End.mul_apply]
    exact congrArg (ρ z) (v.property k)
  obtain ⟨c, hc⟩ := hline ⟨_, hmem⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

end Line

/-! ### Functions satisfying the Hecke relations -/

section Functions

variable {r : ℕ} {θ : upperUnipotent (r + 1) F.Carrier →* ℂˣ}

/-- A `θ`-equivariant right `GL_(r+1)(O)`-invariant function on which every standard
coset sum and the central element `ϖ⁻¹` act by scalars, and which vanishes at the
identity, vanishes identically. -/
theorem eq_zero_of_hecke_relations
    (hθK : IsIntegrallyTrivial (ValuativeRel.valuation F.Carrier) θ)
    (hθ : ∀ i : Fin r, ∃ x : F.Carrier,
      ValuativeRel.valuation F.Carrier x *
        ValuativeRel.valuation F.Carrier (F.canonicalTopologicalData.uniformizerUnit : F.Carrier)
          ≤ 1 ∧ θ (adjacentUnit i x) ≠ 1)
    {f : Langlands.GeneralLinear (r + 1) F.Carrier → ℂ}
    (hf : ∀ (u : upperUnipotent (r + 1) F.Carrier) g, f (u.val * g) = (θ u : ℂ) * f g)
    (hfK : ∀ g, ∀ k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer r,
      f (g * k) = f g)
    (hrec : ∀ (k : ℕ), 1 ≤ k → k ≤ r + 1 → ∃ c : ℂ, ∀ x,
      ∑ α : CosetIndex F.canonicalTopologicalData.ResidueField (r + 1) k,
        f (x * labelledRep F.canonicalTopologicalData.uniformizerUnit (residueLift F) α) =
          c * f x)
    (hcent : ∃ c : ℂ, ∀ x, f (x * torus F.canonicalTopologicalData.uniformizerUnit
      (fun _ : Fin (r + 1) => (-1 : ℤ))) = c * f x)
    (h1 : f 1 = 0) : f = 0 := by
  classical
  set ϖ := F.canonicalTopologicalData.uniformizerUnit with hϖdef
  have hϖ : IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ :=
    uniformizerUnit_isUniformizingElement F
  let d : (Fin (r + 1) → ℤ) → ℂ := fun lam => f (torus ϖ lam)
  have hanti : ∀ lam, ¬ Antitone lam → d lam = 0 := fun lam hlam =>
    eval_torus_eq_zero_of_not_antitone hϖ hf hfK hθ hlam
  have hd0 : d 0 = 0 := by
    have : torus ϖ (0 : Fin (r + 1) → ℤ) = 1 := by
      rw [torus]
      simp only [Pi.zero_apply, zpow_zero]
      exact map_one diagonalUnits
    change f (torus ϖ 0) = 0
    rw [this]
    exact h1
  have hd : SatisfiesHeckeRecursion
      (fun S => ((Fintype.card F.canonicalTopologicalData.ResidueField : ℂ) ^
        Fintype.card (RadicalPairs S))) d := by
    intro lam hlam k hk1 hkm
    obtain ⟨c, hc⟩ := hrec k hk1 hkm
    refine ⟨c, ?_⟩
    rw [← hc (torus ϖ lam),
      sum_eval_torus_mul_labelledRep hϖ.1.le hθK hf (residueLift_mem F) hlam.1 k]
  have hpow : ∀ k, k ≤ r + 1 →
      ((Fintype.card F.canonicalTopologicalData.ResidueField : ℂ) ^
        Fintype.card (RadicalPairs (initialSegment (r + 1) k))) ≠ 0 := by
    intro k _
    apply pow_ne_zero
    exact_mod_cast Fintype.card_ne_zero
  have hpart := eq_zero_of_satisfiesHeckeRecursion hpow hd hanti hd0
  obtain ⟨c', hc'⟩ := hcent
  have hshift : ∀ lam : Fin (r + 1) → ℤ, d (lam + fun _ => -1) = c' * d lam := by
    intro lam
    change f (torus ϖ (lam + fun _ => -1)) = c' * f (torus ϖ lam)
    rw [← torus_mul_torus, hc']
  have hshiftN : ∀ (j : ℕ) (lam : Fin (r + 1) → ℤ),
      d (lam + fun _ => -(j : ℤ)) = c' ^ j * d lam := by
    intro j
    induction j with
    | zero =>
      intro lam
      simp only [Nat.cast_zero, neg_zero, pow_zero, one_mul]
      congr 1
      funext i
      simp
    | succ j ih =>
      intro lam
      have : (lam + fun _ => -((j + 1 : ℕ) : ℤ)) =
          (lam + fun _ => -(j : ℤ)) + fun _ => -1 := by
        funext i
        simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one]
        ring
      rw [this, hshift, ih, pow_succ]
      ring
  have hall : ∀ lam, d lam = 0 := by
    intro lam
    by_cases hlam : Antitone lam
    · set N : ℕ := (-lam (Fin.last r)).toNat
      have hpos : IsPartitionExponent (lam + fun _ => (N : ℤ)) := by
        refine ⟨fun i j hij => ?_, fun i => ?_⟩
        · simp only [Pi.add_apply]
          have := hlam hij
          omega
        · simp only [Pi.add_apply]
          have h1 := hlam (Fin.le_last i)
          have h2 : -lam (Fin.last r) ≤ (N : ℤ) := Int.self_le_toNat _
          omega
      have := hshiftN N (lam + fun _ => (N : ℤ))
      have heq : ((lam + fun _ => (N : ℤ)) + fun _ => -(N : ℤ)) = lam := by
        funext i
        simp
      rw [heq, hpart _ hpos, mul_zero] at this
      exact this
    · exact hanti lam hlam
  funext g
  obtain ⟨k, hk, hg⟩ := exists_eq_unipotentPart hϖ g
  rw [hg, hfK _ _ hk, hf, Pi.zero_apply]
  have := hall (exponent hϖ g)
  change f (torus ϖ (exponent hϖ g)) = 0 at this
  rw [this, mul_zero]

end Functions

/-! ### Matrix coefficients of spherical vectors -/

section Coefficients

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {θ : upperUnipotent (r + 1) F.Carrier →* ℂˣ}
variable (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)

/-- Let the spherical fixed space of a smooth representation be spanned by each of its
nonzero vectors. For a `θ`-equivariant functional `ℓ` and a spherical vector `v` with
`ℓ v = 0`, the whole coefficient `g ↦ ℓ (π g v)` vanishes. -/
theorem coefficient_eq_zero_of_eval_one (hπ : IsSmooth π)
    (hθK : IsIntegrallyTrivial (ValuativeRel.valuation F.Carrier) θ)
    (hθ : ∀ i : Fin r, ∃ x : F.Carrier,
      ValuativeRel.valuation F.Carrier x *
        ValuativeRel.valuation F.Carrier (F.canonicalTopologicalData.uniformizerUnit : F.Carrier)
          ≤ 1 ∧ θ (adjacentUnit i x) ≠ 1)
    (ℓ : functionals (upperUnipotent (r + 1) F.Carrier) θ π)
    (hline : ∀ v w : fixedVectors π (sphericalSubgroup F r), v ≠ 0 → ∃ c : ℂ, c • v = w)
    (v : fixedVectors π (sphericalSubgroup F r)) (h1 : ℓ.val (v : V) = 0)
    (g : Langlands.GeneralLinear (r + 1) F.Carrier) : ℓ.val (π g v) = 0 := by
  by_cases hv : v = 0
  · rw [hv, Submodule.coe_zero, map_zero, map_zero]
  have hspan := hline v
  have key : (fun g => ℓ.val (π g v)) = 0 := by
    refine eq_zero_of_hecke_relations F hθK hθ ?_ ?_ ?_ ?_ ?_
    · intro u g
      rw [map_mul, Module.End.mul_apply]
      exact ℓ.property u _
    · intro g k hk
      rw [map_mul, Module.End.mul_apply]
      exact congrArg (fun w => ℓ.val (π g w)) (v.property ⟨k, hk⟩)
    · intro k hk1 hkm
      obtain ⟨c, hc⟩ := exists_labelledRep_sum_eq_smul F π hπ v (fun w => hspan w hv)
        ⟨k, by omega⟩
      refine ⟨c, fun x => ?_⟩
      have hc' := congrArg (fun w => ℓ.val (π x w)) hc
      simp only [map_sum, map_smul, smul_eq_mul] at hc'
      rw [← hc']
      refine Finset.sum_congr rfl fun α _ => ?_
      change ℓ.val (π (x * _) v) = _
      rw [map_mul, Module.End.mul_apply]
    · obtain ⟨c, hc⟩ := exists_central_smul F π v (fun w => hspan w hv) _
        (torus_const_commute F F.canonicalTopologicalData.uniformizerUnit (-1))
      refine ⟨c, fun x => ?_⟩
      have hc' := congrArg (fun w => ℓ.val (π x w)) hc
      simp only [map_smul, smul_eq_mul] at hc'
      rw [← hc']
      change ℓ.val (π (x * _) v) = _
      rw [map_mul, Module.End.mul_apply]
    · rw [map_one, Module.End.one_apply]
      exact h1
  exact congrFun key g

/-- A vector whose coefficient function is right `GL_(r+1)(O)`-invariant is itself fixed,
when the coefficient map is injective. -/
theorem mem_fixedVectors_of_model (ℓ : functionals (upperUnipotent (r + 1) F.Carrier) θ π)
    (hinj : Function.Injective (modelMap π ℓ)) (v : V)
    (hvK : ∀ k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer r,
      ∀ g, (modelMap π ℓ v).val.val (g * k) = (modelMap π ℓ v).val.val g) :
    v ∈ fixedVectors π (sphericalSubgroup F r) := by
  intro k
  change π k.val v = v
  apply hinj
  rw [(modelMap π ℓ).isIntertwining]
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact hvK k.val k.property g

/-- Under the hypotheses of `coefficient_eq_zero_of_eval_one`, for an irreducible
representation and a nonzero functional, the model of `ℓ` contains exactly one
normalized spherical vector when the spherical fixed space is nonzero. -/
theorem existsUnique_sphericalTest (hπ : IsSmooth π) [Representation.IsIrreducible π]
    (hθK : IsIntegrallyTrivial (ValuativeRel.valuation F.Carrier) θ)
    (hθ : ∀ i : Fin r, ∃ x : F.Carrier,
      ValuativeRel.valuation F.Carrier x *
        ValuativeRel.valuation F.Carrier (F.canonicalTopologicalData.uniformizerUnit : F.Carrier)
          ≤ 1 ∧ θ (adjacentUnit i x) ≠ 1)
    (ℓ : functionals (upperUnipotent (r + 1) F.Carrier) θ π) (hℓ : ℓ.val ≠ 0)
    (hline : ∀ v w : fixedVectors π (sphericalSubgroup F r), v ≠ 0 → ∃ c : ℂ, c • v = w)
    (hK : fixedVectors π (sphericalSubgroup F r) ≠ ⊥) :
    ∃ w : SphericalTest π ℓ, ∀ w' : SphericalTest π ℓ, w' = w := by
  have hinj : Function.Injective (modelMap π ℓ) := (modelEquiv π ℓ hℓ).injective
  have hval : ∀ (v : V) g, (modelMap π ℓ v).val.val g = ℓ.val (π g v) := fun _ _ => rfl
  -- a spherical vector with `ℓ v = 0` is zero
  have hzero : ∀ v : fixedVectors π (sphericalSubgroup F r), ℓ.val (v : V) = 0 → v = 0 := by
    intro v h1
    have hc := coefficient_eq_zero_of_eval_one F π hπ hθK hθ ℓ hline v h1
    apply Subtype.ext
    apply hinj
    rw [Submodule.coe_zero, map_zero]
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact hc g
  -- model vectors of spherical tests come from spherical vectors
  have hpre : ∀ w : SphericalTest π ℓ, ∃ v : fixedVectors π (sphericalSubgroup F r),
      modelMap π ℓ v = w.val.val ∧ ℓ.val (v : V) = 1 := by
    intro w
    obtain ⟨v, hv⟩ := modelMap_surjective π ℓ w.val.val
    have hwK := (mem_sphericalModelSpace π ℓ w.val.val).1 w.val.property
    have hvK : v ∈ fixedVectors π (sphericalSubgroup F r) :=
      mem_fixedVectors_of_model F π ℓ hinj v (by rw [hv]; exact hwK)
    refine ⟨⟨v, hvK⟩, hv, ?_⟩
    have h1 := w.property
    change (w.val.val : (coefficientModel π ℓ).toSubmodule).val.val 1 = 1 at h1
    rw [← hv, hval, map_one, Module.End.one_apply] at h1
    exact h1
  -- existence
  obtain ⟨v, hvK, hv0⟩ := (Submodule.ne_bot_iff _).1 hK
  have hWmem : modelMap π ℓ v ∈ sphericalModelSpace π ℓ := by
    rw [mem_sphericalModelSpace]
    intro k hk g
    rw [hval, hval, map_mul, Module.End.mul_apply]
    exact congrArg (fun w => ℓ.val (π g w)) (hvK ⟨k, hk⟩)
  have hW1 : modelEvaluation π ℓ (modelMap π ℓ v) ≠ 0 := by
    intro h
    change (modelMap π ℓ v).val.val 1 = 0 at h
    rw [hval, map_one, Module.End.one_apply] at h
    exact hv0 (congrArg Subtype.val (hzero ⟨v, hvK⟩ h))
  refine ⟨normalizeSphericalTest π ℓ ⟨modelMap π ℓ v, hWmem⟩ hW1, fun w' => ?_⟩
  -- uniqueness
  set w := normalizeSphericalTest π ℓ ⟨modelMap π ℓ v, hWmem⟩ hW1
  obtain ⟨u, hu, hu1⟩ := hpre w
  obtain ⟨u', hu', hu1'⟩ := hpre w'
  have hdiff := hzero (u' - u) (by
    rw [Submodule.coe_sub, map_sub, hu1, hu1', sub_self])
  have hEq : u' = u := sub_eq_zero.1 hdiff
  apply Subtype.ext
  apply Subtype.ext
  rw [← hu, ← hu', hEq]

end Coefficients

/-! ### Standard characters of conductor `O` -/

section Conductor

variable {r : ℕ}

theorem standardCharacter_adjacentUnit (ψ : UnitaryAdditiveCharacter F.Carrier) (i : Fin r)
    (x : F.Carrier) :
    (standardCharacter ψ r (adjacentUnit i x) : ℂ) = ψ.complex x := by
  rw [standardCharacter_apply]
  congr 1
  rw [Finset.sum_eq_single i]
  · change Matrix.transvection i.castSucc i.succ x i.castSucc i.succ = x
    rw [transvection_apply]
    simp [Fin.castSucc_lt_succ.ne]
  · intro k _ hk
    change Matrix.transvection i.castSucc i.succ x k.castSucc k.succ = 0
    have h1 : k.castSucc ≠ k.succ := Fin.castSucc_lt_succ.ne
    have h2 : ¬ (i.castSucc = k.castSucc ∧ i.succ = k.succ) := fun h =>
      hk (Fin.castSucc_injective _ h.1).symm
    rw [transvection_apply]
    simp only [h1, h2, ite_false, add_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- An additive character of conductor `O` is nontrivial on `ϖ⁻¹ O`. -/
theorem exists_conductor_witness (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : HasIntegerConductor ψ) :
    ∃ x : F.Carrier,
      ValuativeRel.valuation F.Carrier x *
        ValuativeRel.valuation F.Carrier (F.canonicalTopologicalData.uniformizerUnit : F.Carrier)
          ≤ 1 ∧ ψ x ≠ 1 := by
  set ϖ := F.canonicalTopologicalData.uniformizerUnit
  have hϖ : IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ :=
    uniformizerUnit_isUniformizingElement F
  have hv0 : 0 < ValuativeRel.valuation F.Carrier (ϖ : F.Carrier) :=
    valuation_pos _ ϖ
  have hnot : ((ϖ⁻¹ : F.Carrierˣ) : F.Carrier) ∉ (ValuativeRel.valuation F.Carrier).integer := by
    rw [Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀, not_le]
    exact one_lt_inv_iff₀.2 ⟨hv0, hϖ.1⟩
  have : ¬ ∀ y ∈ (ValuativeRel.valuation F.Carrier).integer,
      ψ (((ϖ⁻¹ : F.Carrierˣ) : F.Carrier) * y) = 1 := fun h => hnot (hψ.2 _ h)
  push Not at this
  obtain ⟨y, hy, hψy⟩ := this
  refine ⟨((ϖ⁻¹ : F.Carrierˣ) : F.Carrier) * y, ?_, hψy⟩
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, mul_comm, ← mul_assoc,
    mul_inv_cancel₀ hv0.ne', one_mul]
  exact (Valuation.mem_integer_iff _ _).1 hy

theorem standardCharacter_nondegenerate (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : HasIntegerConductor ψ) (i : Fin r) :
    ∃ x : F.Carrier,
      ValuativeRel.valuation F.Carrier x *
        ValuativeRel.valuation F.Carrier (F.canonicalTopologicalData.uniformizerUnit : F.Carrier)
          ≤ 1 ∧ standardCharacter ψ r (adjacentUnit i x) ≠ 1 := by
  obtain ⟨x, hx, hψx⟩ := exists_conductor_witness F ψ hψ
  refine ⟨x, hx, fun h => hψx ?_⟩
  have h' := congrArg (fun u : ℂˣ => (u : ℂ)) h
  simp only [standardCharacter_adjacentUnit, Units.val_one,
    UnitaryAdditiveCharacter.complex_apply] at h'
  exact Subtype.ext h'

theorem inverseStandardCharacter_nondegenerate (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : HasIntegerConductor ψ) (i : Fin r) :
    ∃ x : F.Carrier,
      ValuativeRel.valuation F.Carrier x *
        ValuativeRel.valuation F.Carrier (F.canonicalTopologicalData.uniformizerUnit : F.Carrier)
          ≤ 1 ∧ inverseStandardCharacter ψ r (adjacentUnit i x) ≠ 1 := by
  obtain ⟨x, hx, hne⟩ := standardCharacter_nondegenerate F ψ hψ i
  refine ⟨x, hx, fun h => hne ?_⟩
  change (standardCharacter ψ r (adjacentUnit i x))⁻¹ = 1 at h
  exact inv_eq_one.1 h

end Conductor

/-! ### The statement -/

theorem fixedLine_of_isGeneric {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hirr : Representation.IsIrreducible π) (hadm : IsAdmissible π)
    (hK : fixedVectors π (sphericalSubgroup F r) ≠ ⊥) :
    ∀ v w : fixedVectors π (sphericalSubgroup F r), v ≠ 0 → ∃ c : ℂ, c • v = w := by
  let A : AutomorphicObject.{uF, uV} F r.succPNat := ⟨SmoothRep.of π hadm.1, hirr, hadm⟩
  have hline : Module.finrank ℂ (fixedVectors π (sphericalSubgroup F r)) = 1 :=
    sphericalFixedLine p F r A hK
  intro v w hv
  exact (finrank_eq_one_iff_of_nonzero' v hv).1 hline w

end Langlands.RankinSelberg.UnramifiedWhittaker

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear.Iwasawa Langlands.Whittaker
open Langlands.RankinSelberg.UnramifiedWhittaker Langlands.Unramified

universe uF uV

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup

/-- Jacquet–Shalika, *Euler products II*, §1.3: unique normalized spherical vectors in
the Whittaker models for `ψ` and `ψ⁻¹` of an unramified generic representation, when `ψ`
has conductor `O`. -/
theorem unramifiedSphericalVector : UnramifiedSphericalVectorStatement.{uF, uV} := by
  intro p _ F r V _ _ π ψ hψ hgen hK
  obtain ⟨hirr, hadm, -⟩ := hgen
  have := hirr
  have hline := fixedLine_of_isGeneric F π hirr hadm hK
  refine ⟨fun ℓ hℓ => ?_, fun ℓ hℓ => ?_⟩
  · exact existsUnique_sphericalTest F π hadm.1
      (isIntegrallyTrivial_standardCharacter hψ.1 r)
      (standardCharacter_nondegenerate F ψ hψ) ℓ hℓ hline hK
  · exact existsUnique_sphericalTest F π hadm.1
      (isIntegrallyTrivial_inverseStandardCharacter hψ.1 r)
      (inverseStandardCharacter_nondegenerate F ψ hψ) ℓ hℓ hline hK

end Langlands.RankinSelberg
