import Langlands.Algebra.LocalDivisionIntegerLattice
import Langlands.Algebra.LocalDivisionResidueSubfield
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.Dimension.Free

/-! Finite valuation layers over an original full-residue subfield. -/

noncomputable section

namespace Langlands.CentralDivision

open ValuativeRel
open scoped WithZero

universe u uL

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- One original representative of each attained nonpositive integer value. -/
def localDivisionValuationLayerRepresentative (i : ℕ) : D := by
  classical
  exact if h : ∃ x : D, localReducedNormIntValuation K D x = WithZero.exp (-(i : ℤ))
  then h.choose else 0

/-- An attained layer has precisely the value of its original representative. -/
theorem localDivisionValuationLayerRepresentative_value (i : ℕ)
    (h : ∃ x : D, localReducedNormIntValuation K D x = WithZero.exp (-(i : ℤ))) :
    localReducedNormIntValuation K D (localDivisionValuationLayerRepresentative K D i) =
      WithZero.exp (-(i : ℤ)) := by
  simp only [localDivisionValuationLayerRepresentative, dite_eq_left h]
  exact h.choose_spec

private theorem intValue_lt_layer_iff (a : ℤᵐ⁰) (i : ℕ) :
    a < WithZero.exp (-(i : ℤ)) ↔ a ≤ WithZero.exp (-((i + 1 : ℕ) : ℤ)) := by
  have he : (WithZero.exp (-((i + 1 : ℕ) : ℤ)) : ℤᵐ⁰) * WithZero.exp 1 =
      WithZero.exp (-(i : ℤ)) := by
    rw [← WithZero.exp_add]
    congr 1
    omega
  simpa only [he] using (WithZero.lt_mul_exp_iff_le (x := a)
    (y := WithZero.exp (-((i + 1 : ℕ) : ℤ))) WithZero.exp_ne_zero)

local instance degreeIntegerAlgebra : Algebra 𝒪[K] D :=
  Algebra.compHom D (algebraMap 𝒪[K] K)

local instance degreeIntegerTower : IsScalarTower 𝒪[K] K D :=
  .of_algebraMap_smul (fun _ _ => rfl)

/-- An original base integer in the Jacobson radical has precisely n levels in D. -/
theorem exists_localDivision_scalar_valuation_step :
    ∃ p : 𝒪[K], (p : K) ≠ 0 ∧ p ∈ Ideal.jacobson (⊥ : Ideal 𝒪[K]) ∧
      localReducedNormIntValuation K D (algebraMap K D (p : K)) =
        WithZero.exp (-(CentralSimple.reducedDegree K D : ℤ)) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  obtain ⟨p, hp⟩ := ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-1 : ℤ)))
  have he : e (valuation K p) = WithZero.exp (-1 : ℤ) := by
    rw [hp, e.apply_symm_apply]
  have hlt : valuation K p < 1 := by
    apply e.toOrderIso.lt_iff_lt.mp
    change e (valuation K p) < e 1
    rw [he, map_one]
    simp
  have hp0 : p ≠ 0 := by
    intro hz
    have hz' : (0 : ℤᵐ⁰) = WithZero.exp (-1 : ℤ) := by simpa only [hz, map_zero] using he
    exact WithZero.exp_ne_zero hz'.symm
  let q : 𝒪[K] := ⟨p, hlt.le⟩
  refine ⟨q, hp0, ?_, ?_⟩
  · rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hq
    have h1 := (DivisionValuation.isUnit_iff_value_eq_one (valuation K) q).mp hq
    exact hlt.ne h1
  · rw [localReducedNormIntValuation_algebraMap]
    change e (valuation K p) ^ _ = _
    rw [he, ← WithZero.exp_nsmul]
    simp only [nsmul_eq_mul, mul_neg, mul_one]

section Embedding

variable {L : Type uL} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

/-- Full actual residue improves any original element by a subfield multiple
of an original element of the same nonzero value. -/
theorem exists_localDivisionSubfield_valuation_improvement
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (x t : D) (ht : t ≠ 0)
    (hxt : localReducedNormValuation K D x = localReducedNormValuation K D t) :
    ∃ c : L, localReducedNormValuation K D (x - ι c * t) <
      localReducedNormValuation K D t := by
  let v := localReducedNormValuation K D
  have hvt : v t ≠ 0 := (map_ne_zero v).mpr ht
  let z : v.integer := ⟨x * t⁻¹, by
    change v (x * t⁻¹) ≤ 1
    rw [map_mul, v.map_inv, hxt, mul_inv_cancel₀ hvt]⟩
  obtain ⟨r, hr⟩ := hsurj (DivisionValuation.reduction v z)
  obtain ⟨c, hc⟩ := DivisionValuation.reduction_surjective
    (localDivisionSubfieldValuation K D ι) r
  have heq : DivisionValuation.reduction v z =
      DivisionValuation.reduction v (localDivisionSubfieldIntegerMap K D ι c) := by
    rw [← localDivisionSubfieldResidueMap_reduction, hc, hr]
  have hsmall := (DivisionValuation.reduction_eq_iff v _ _).mp heq
  refine ⟨c.val, ?_⟩
  have he : x - ι c.val * t = (x * t⁻¹ - ι c.val) * t := by
    rw [sub_mul, mul_assoc, inv_mul_cancel₀ ht, mul_one]
  change v (x - ι c.val * t) < v t
  rw [he, map_mul]
  exact (mul_lt_mul_of_pos_right hsmall (pos_iff_ne_zero.mpr hvt)).trans_eq (one_mul _)

/-- The same improvement in the intrinsic integer-valued normalization. -/
theorem exists_localDivisionSubfield_intValuation_improvement
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (x t : D) (ht : t ≠ 0)
    (hxt : localReducedNormIntValuation K D x = localReducedNormIntValuation K D t) :
    ∃ c : L, localReducedNormIntValuation K D (x - ι c * t) <
      localReducedNormIntValuation K D t := by
  have heq : localReducedNormValuation K D x = localReducedNormValuation K D t :=
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective hxt
  obtain ⟨c, hc⟩ := exists_localDivisionSubfield_valuation_improvement K D ι
    hsurj x t ht heq
  exact ⟨c, (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).strictMono hc⟩

/-- The left action of the original embedded field, without a false central algebra structure. -/
@[instance_reducible]
def localDivisionSubfieldLeftModule : Module L D := Module.compHom D ι.toRingHom

/-- One original valuation layer is removed by an element of the given subfield span. -/
theorem exists_localDivisionSubfield_layer_approximation
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    : letI := localDivisionSubfieldLeftModule K D ι
      ∀ (N : Submodule L D) (i : ℕ),
      localDivisionValuationLayerRepresentative K D i ∈ N →
      ∀ x : D, localReducedNormIntValuation K D x ≤ WithZero.exp (-(i : ℤ)) →
      ∃ s ∈ N, localReducedNormIntValuation K D (x - s) ≤
        WithZero.exp (-((i + 1 : ℕ) : ℤ)) := by
  let := localDivisionSubfieldLeftModule K D ι
  intro N i htN x hx
  by_cases heq : localReducedNormIntValuation K D x = WithZero.exp (-(i : ℤ))
  · have ht := localDivisionValuationLayerRepresentative_value K D i ⟨x, heq⟩
    have ht0 : localDivisionValuationLayerRepresentative K D i ≠ 0 := by
      intro h
      rw [h, map_zero] at ht
      exact WithZero.exp_ne_zero ht.symm
    obtain ⟨c, hc⟩ := exists_localDivisionSubfield_intValuation_improvement K D ι
      hsurj x (localDivisionValuationLayerRepresentative K D i) ht0 (heq.trans ht.symm)
    refine ⟨c • localDivisionValuationLayerRepresentative K D i, N.smul_mem c htN, ?_⟩
    apply (intValue_lt_layer_iff _ i).mp
    change localReducedNormIntValuation K D
      (x - ι c * localDivisionValuationLayerRepresentative K D i) < _
    simpa only [ht] using hc
  · refine ⟨0, N.zero_mem, ?_⟩
    simpa only [sub_zero] using (intValue_lt_layer_iff _ i).mp (lt_of_le_of_ne hx heq)

/-- Finitely many original representatives approximate every actual integer element. -/
theorem exists_localDivisionSubfield_finite_layer_approximation
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    : letI := localDivisionSubfieldLeftModule K D ι
      ∀ (N : Submodule L D) (n : ℕ),
      (∀ i < n, localDivisionValuationLayerRepresentative K D i ∈ N) →
      ∀ x : D, localReducedNormIntValuation K D x ≤ 1 →
      ∃ s ∈ N, localReducedNormIntValuation K D (x - s) ≤ WithZero.exp (-(n : ℤ)) := by
  let := localDivisionSubfieldLeftModule K D ι
  intro N n htN x hx
  have happrox : ∀ k : ℕ, k ≤ n → ∃ s ∈ N,
      localReducedNormIntValuation K D (x - s) ≤ WithZero.exp (-(k : ℤ)) := by
    intro k
    induction k with
    | zero =>
        intro _
        exact ⟨0, N.zero_mem, by simpa using hx⟩
    | succ k ih =>
        intro hk
        obtain ⟨s, hs, hxs⟩ := ih (by omega)
        obtain ⟨t, ht, hxst⟩ := exists_localDivisionSubfield_layer_approximation K D ι
          hsurj N k (htN k (by omega)) (x - s) hxs
        exact ⟨s + t, N.add_mem hs ht, by simpa only [sub_sub] using hxst⟩
  exact happrox n le_rfl

/-- The n original valuation-layer representatives span D over every full-residue subfield. -/
theorem localDivisionSubfield_layer_span_eq_top
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι)) :
    letI := localDivisionSubfieldLeftModule K D ι
    Submodule.span L (Set.range (fun i : Fin (CentralSimple.reducedDegree K D) =>
      localDivisionValuationLayerRepresentative K D i.val)) = ⊤ := by
  let := localDivisionSubfieldLeftModule K D ι
  let : IsScalarTower K L D := ⟨fun k l x => by
    change ι (k • l) * x = k • (ι l * x)
    rw [map_smul, smul_mul_assoc]⟩
  let : Algebra 𝒪[K] L := Algebra.compHom L (algebraMap 𝒪[K] K)
  let : IsScalarTower 𝒪[K] L D := .of_algebraMap_smul (fun c x => by
    change algebraMap K L (c : K) • x = c • x
    rw [IsScalarTower.algebraMap_smul L]
    exact (IsScalarTower.algebraMap_smul K c x).symm)
  let n := CentralSimple.reducedDegree K D
  let N := Submodule.span L (Set.range (fun i : Fin n =>
    localDivisionValuationLayerRepresentative K D i.val))
  let A := localDivisionIntegerLattice K D
  have hfinite : A.FG := Module.Finite.iff_fg.mp (localDivisionIntegerLattice_finite K D)
  obtain ⟨p, hp0, hpjac, hpval⟩ := exists_localDivision_scalar_valuation_step K D
  let I : Ideal 𝒪[K] := Ideal.span {p}
  have hI : I ≤ Ideal.jacobson (⊥ : Ideal 𝒪[K]) :=
    (Ideal.span_singleton_le_iff_mem _).mpr hpjac
  have hmod : A ≤ N.restrictScalars 𝒪[K] ⊔ I • A := by
    intro x hx
    have hxw : localReducedNormIntValuation K D x ≤ 1 := by
      change localReducedNormValuation K D x ≤ 1 at hx
      rw [← map_one (localReducedNormIntValuation K D)]
      exact (localReducedNormIntValuation_le_iff K D x 1).mpr
        (by simpa only [map_one] using hx)
    obtain ⟨s, hs, hxs⟩ := exists_localDivisionSubfield_finite_layer_approximation K D ι
      hsurj N n (fun i hi => Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩) x hxw
    let y := (algebraMap K D (p : K))⁻¹ * (x - s)
    have hpy0 : localReducedNormIntValuation K D (algebraMap K D (p : K)) ≠ 0 :=
      (map_ne_zero _).mpr ((map_ne_zero _).mpr hp0)
    have hyw : localReducedNormIntValuation K D y ≤ 1 := by
      change localReducedNormIntValuation K D
        ((algebraMap K D (p : K))⁻¹ * (x - s)) ≤ 1
      rw [map_mul, Valuation.map_inv]
      apply (mul_le_mul_of_nonneg_left (hxs.trans_eq hpval.symm) zero_le).trans
      rw [inv_mul_cancel₀ hpy0]
    have hy : y ∈ A := by
      change localReducedNormValuation K D y ≤ 1
      rw [← map_one (localReducedNormValuation K D)]
      apply (localReducedNormIntValuation_le_iff K D y 1).mp
      simpa only [map_one] using hyw
    have hpy : x - s = p • y := by
      rw [← IsScalarTower.algebraMap_smul K p y, Algebra.smul_def]
      change x - s = algebraMap K D (p : K) *
        ((algebraMap K D (p : K))⁻¹ * (x - s))
      rw [← mul_assoc, mul_inv_cancel₀ ((map_ne_zero _).mpr hp0), one_mul]
    have hsmall : x - s ∈ I • A := by
      rw [hpy]
      exact Submodule.smul_mem_smul (Ideal.subset_span (by simp)) hy
    exact Submodule.mem_sup.mpr ⟨s, hs, x - s, hsmall, add_sub_cancel _ _⟩
  have hAN : A ≤ N.restrictScalars 𝒪[K] :=
    Submodule.le_of_le_smul_of_le_jacobson_bot hfinite hI hmod
  have hspan : Submodule.span K (A : Set D) ≤ N.restrictScalars K :=
    Submodule.span_le.mpr hAN
  rw [localDivisionIntegerLattice_span K D] at hspan
  apply top_unique
  intro x _
  exact hspan (by trivial)

/-- A full-residue embedded field leaves at most n left-module dimensions in D. -/
theorem localDivisionSubfield_finrank_le
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι)) :
    letI := localDivisionSubfieldLeftModule K D ι
    Module.finrank L D ≤ CentralSimple.reducedDegree K D := by
  let := localDivisionSubfieldLeftModule K D ι
  simpa only [Fintype.card_fin] using
    (finrank_le_of_span_eq_top (localDivisionSubfield_layer_span_eq_top K D ι hsurj))

/-- Every original full-residue subfield has degree at least the reduced degree. -/
theorem reducedDegree_le_localDivisionSubfield_finrank
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι)) :
    CentralSimple.reducedDegree K D ≤ Module.finrank K L := by
  let := localDivisionSubfieldLeftModule K D ι
  let : IsScalarTower K L D := ⟨fun k l x => by
    change ι (k • l) * x = k • (ι l * x)
    rw [map_smul, smul_mul_assoc]⟩
  let : FiniteDimensional K L := FiniteDimensional.of_injective ι.toLinearMap ι.injective
  let : FiniteDimensional L D := Module.Finite.of_restrictScalars_finite K L D
  have hdim := Module.finrank_mul_finrank K L D
  rw [CentralSimple.finrank_eq_reducedDegree_mul_self K D] at hdim
  have hle := localDivisionSubfield_finrank_le K D ι hsurj
  have hmul := Nat.mul_le_mul_left (Module.finrank K L) hle
  nlinarith [CentralSimple.reducedDegree_pos K D]

end Embedding

end Langlands.CentralDivision
