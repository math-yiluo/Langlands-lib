import Langlands.Algebra.LocalDivisionReducedDegree
import Langlands.Algebra.DivisionFieldEmbeddingsProof

/-!
# Conjugation on the residue ring of a division-ring valuation

Conjugation by a unit preserves a valuation with commutative values, so it induces a ring
endomorphism of the residue ring. For a central division algebra over a nonarchimedean local
field, some unit acts on the residue field with order exactly the reduced degree.
-/

noncomputable section

namespace Langlands.DivisionValuation

universe u v

variable {D : Type u} {Γ₀ : Type v} [DivisionRing D]
  [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation D Γ₀)

theorem conj_value (j : Dˣ) (x : D) : v ((j : D) * x * ((j⁻¹ : Dˣ) : D)) = v x := by
  rw [map_mul, map_mul, mul_right_comm, ← map_mul, Units.mul_inv, map_one, one_mul]

/-- Conjugation by a unit on the integer subring. -/
def conjInteger (j : Dˣ) : v.integer →+* v.integer where
  toFun x := ⟨(j : D) * x * ((j⁻¹ : Dˣ) : D), by
    change v _ ≤ 1
    rw [conj_value]
    exact x.prop⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by
    change (j : D) * ((x : D) * (y : D)) * ((j⁻¹ : Dˣ) : D) =
      ((j : D) * x * ((j⁻¹ : Dˣ) : D)) * ((j : D) * y * ((j⁻¹ : Dˣ) : D))
    simp [mul_assoc])
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by
    change (j : D) * ((x : D) + (y : D)) * ((j⁻¹ : Dˣ) : D) =
      ((j : D) * x * ((j⁻¹ : Dˣ) : D)) + ((j : D) * y * ((j⁻¹ : Dˣ) : D))
    rw [mul_add, add_mul])

@[simp]
theorem conjInteger_coe (j : Dˣ) (x : v.integer) :
    (conjInteger v j x : D) = (j : D) * x * ((j⁻¹ : Dˣ) : D) := rfl

/-- Conjugation by a unit on the residue ring. -/
def conjResidue (j : Dˣ) : Residue v →+* Residue v :=
  Ideal.Quotient.lift (strictIdeal v) ((reduction v).comp (conjInteger v j))
    (fun x hx => by
      apply (reduction_eq_zero_iff v _).mpr
      change v ((j : D) * x * ((j⁻¹ : Dˣ) : D)) < 1
      rw [conj_value]
      exact hx)

@[simp]
theorem conjResidue_reduction (j : Dˣ) (x : v.integer) :
    conjResidue v j (reduction v x) = reduction v (conjInteger v j x) := rfl

theorem conjResidue_mul (j k : Dˣ) (r : Residue v) :
    conjResidue v (j * k) r = conjResidue v j (conjResidue v k r) := by
  obtain ⟨x, rfl⟩ := reduction_surjective v r
  simp only [conjResidue_reduction]
  congr 1
  apply Subtype.ext
  simp [mul_assoc]

theorem conjResidue_one (r : Residue v) : conjResidue v 1 r = r := by
  obtain ⟨x, rfl⟩ := reduction_surjective v r
  simp only [conjResidue_reduction]
  congr 1
  apply Subtype.ext
  simp

theorem conjResidue_pow (j : Dˣ) (n : ℕ) (r : Residue v) :
    conjResidue v (j ^ n) r = (conjResidue v j)^[n] r := by
  induction n generalizing r with
  | zero => simpa using conjResidue_one v r
  | succ n ih =>
    rw [pow_succ, conjResidue_mul, Function.iterate_succ_apply, ih]

/-- Units of value one act trivially when the residue ring is commutative. -/
theorem conjResidue_of_value_eq_one (hcomm : ∀ a b : Residue v, a * b = b * a)
    (j : Dˣ) (hj : v (j : D) = 1) (r : Residue v) : conjResidue v j r = r := by
  obtain ⟨x, rfl⟩ := reduction_surjective v r
  have hji : v ((j⁻¹ : Dˣ) : D) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hj, inv_one]
  let jI : v.integer := ⟨j, hj.le⟩
  let jiI : v.integer := ⟨((j⁻¹ : Dˣ) : D), hji.le⟩
  have hc : conjInteger v j x = jI * x * jiI := rfl
  have h1 : jI * jiI = 1 := Subtype.ext (Units.mul_inv j)
  rw [conjResidue_reduction, hc, map_mul, map_mul, mul_assoc, hcomm (reduction v x),
    ← mul_assoc, ← map_mul, h1, map_one, one_mul]

/-- The residue action depends only on the value of the conjugating unit. -/
theorem conjResidue_eq_of_value_eq (hcomm : ∀ a b : Residue v, a * b = b * a)
    (j k : Dˣ) (h : v (j : D) = v (k : D)) (r : Residue v) :
    conjResidue v k r = conjResidue v j r := by
  have hk : k = j * (j⁻¹ * k) := by group
  have hk0 : v (k : D) ≠ 0 := (v.ne_zero_iff).mpr k.ne_zero
  have hv : v (((j⁻¹ * k : Dˣ)) : D) = 1 := by
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, h,
      inv_mul_cancel₀ hk0]
  rw [hk, conjResidue_mul, conjResidue_of_value_eq_one v hcomm _ hv]

end Langlands.DivisionValuation

namespace Langlands.CentralDivision

open ValuativeRel Langlands.DivisionValuation

universe u

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance : Field (Residue (localReducedNormValuation K D)) :=
  localDivisionResidueField K D
local instance : Algebra 𝓀[K] (Residue (localReducedNormValuation K D)) :=
  localDivisionResidueAlgebra K D

/-- Some unit of a local central division algebra acts on the residue field with order
dividing exactly the reduced degree: if its `n`-th power acts trivially, the reduced degree
divides `n`. -/
theorem exists_unit_conjResidue_faithful :
    ∃ u : Dˣ, ∀ n : ℕ,
      (∀ r, conjResidue (localReducedNormValuation K D) (u ^ n) r = r) →
        CentralSimple.reducedDegree K D ∣ n := by
  obtain ⟨f, b, hmon, hres, hmin, hsep, hsurj, hdim⟩ :=
    exists_localDivision_fullResidue_polynomial_subfield K D
  let := residueGeneratorField K D (b : D)
  let E := residueGeneratorSubalgebra K D (b : D)
  let R := Residue (localReducedNormValuation K D)
  have hsepR : (f.map (IsLocalRing.residue 𝒪[K])).Separable := by
    rw [hres]
    exact PerfectField.separable_of_irreducible
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral _))
  have hsplitR :
      ((f.map (IsLocalRing.residue 𝒪[K])).map (algebraMap 𝓀[K] R)).Splits := by
    rw [hres]
    exact IsGalois.splits 𝓀[K] _
  have hsplit : ((minpoly K (b : D)).map (algebraMap K E)).Splits := by
    rw [← hmin]
    exact localDivisionSubfield_splits_base_polynomial K D E.val hsurj f hmon hsepR hsplitR
  let : Polynomial.IsSplittingField K E (minpoly K (b : D)) :=
    residueGenerator_isSplittingField K D (b : D) hsplit
  have hgal : IsGalois K E := IsGalois.of_separable_splitting_field hsep
  let a : (localDivisionSubfieldValuation K D E.val).integer :=
    ⟨⟨(b : D), residueGenerator_mem K D (b : D)⟩, b.prop⟩
  have hroot : f.eval₂ (localDivisionSubfieldBaseIntegerMap K D E.val) a = 0 := by
    let θ : (localDivisionSubfieldValuation K D E.val).integer →+* D :=
      E.val.toRingHom.comp (localDivisionSubfieldValuation K D E.val).integer.subtype
    have hθ : θ.comp (localDivisionSubfieldBaseIntegerMap K D E.val) =
        (algebraMap K D).comp (algebraMap 𝒪[K] K) := by
      ext c
      exact E.val.commutes c.val
    apply (E.val.injective.comp Subtype.val_injective)
    change θ (f.eval₂ (localDivisionSubfieldBaseIntegerMap K D E.val) a) = θ 0
    rw [map_zero, Polynomial.hom_eval₂, hθ, ← Polynomial.eval₂_map]
    change Polynomial.aeval (b : D) (f.map (algebraMap 𝒪[K] K)) = 0
    rw [hmin]
    exact minpoly.aeval K (b : D)
  have hinj := localDivisionSubfieldGaloisReduction_injective K D E.val hsurj
    (residueGeneratorPowerBasis K D (b : D)) a rfl f hroot hsepR
  have hcyc : IsCyclic (E ≃ₐ[K] E) := isCyclic_of_injective _ hinj
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E ≃ₐ[K] E)
  have hord : orderOf g = CentralSimple.reducedDegree K D := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, IsGalois.card_aut_eq_finrank, hdim,
      localDivisionResidue_finrank_eq_reducedDegree]
  obtain ⟨u, hu⟩ := fieldEmbeddingsConjugate K D E (E.val.comp (g : E →ₐ[K] E)) E.val
  have hpow : ∀ (n : ℕ) (x : E), (((g ^ n) x : E) : D) =
      ((u ^ n : Dˣ) : D) * x * (((u ^ n)⁻¹ : Dˣ) : D) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', AlgEquiv.mul_apply]
      have h1 := hu ((g ^ n) x)
      change ((g ((g ^ n) x) : E) : D) = (u : D) * (((g ^ n) x : E) : D) * ((u⁻¹ : Dˣ) : D)
        at h1
      rw [h1, ih x, pow_succ', mul_inv_rev]
      simp only [Units.val_mul, mul_assoc]
  refine ⟨u, fun n hn => ?_⟩
  rw [← hord]
  apply orderOf_dvd_of_pow_eq_one
  apply hinj
  rw [map_pow, map_one]
  refine AlgEquiv.ext fun z => ?_
  obtain ⟨z₀, rfl⟩ := hsurj z
  obtain ⟨w, rfl⟩ := reduction_surjective _ z₀
  rw [AlgEquiv.one_apply, ← map_pow]
  change localDivisionSubfieldFullResidueAut K D E.val hsurj (g ^ n) _ = _
  rw [localDivisionSubfieldFullResidueAut_reduction]
  change reduction _ (localDivisionSubfieldIntegerMap K D E.val
      (localDivisionSubfieldIntegerAut K D E.val (g ^ n) w)) =
    reduction _ (localDivisionSubfieldIntegerMap K D E.val w)
  have hn' := hn (reduction _ (localDivisionSubfieldIntegerMap K D E.val w))
  rw [conjResidue_reduction] at hn'
  rw [← hn']
  congr 1
  apply Subtype.ext
  change (((g ^ n) (w : E) : E) : D) = _
  rw [hpow]
  rfl

end Langlands.CentralDivision
