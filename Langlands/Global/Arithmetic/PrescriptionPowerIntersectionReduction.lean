import Langlands.Global.Arithmetic.PrescriptionFiniteQuotientStatement

/-! # The actual local-product power intersection from global half-power descent -/

noncomputable section

universe u

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))

/-- Extract the whole infinite coordinate and the selected finite coordinates.
Only the algebraic retraction is needed for the power-intersection argument. -/
def prescriptionIdeleRetraction : Ideles K →* PrescriptionLocalProduct K S where
  toFun x := ((ideleProductEquiv K x).1, fun v => finiteIdeleProjection K v.1 x)
  map_one' := by
    simp only [map_one, Prod.fst_one]
    rfl
  map_mul' x y := by
    simp only [map_mul, Prod.fst_mul]
    rfl

private theorem finiteProjection_infiniteIdeles (v : FinitePlace K)
    (a : (InfiniteAdeles K)ˣ) :
    finiteIdeleProjection K v (infiniteIdelesInclusion K a) = 1 := by
  apply Units.ext
  rfl

private theorem finiteProjection_finiteInclusion_ne (v w : FinitePlace K) (h : v ≠ w)
    (a : (FiniteCompletion K w)ˣ) :
    finiteIdeleProjection K v (finiteIdeleInclusion K w a) = 1 := by
  classical
  apply Units.ext
  exact Pi.mulSingle_eq_of_ne h a.val

private theorem infinitePart_infiniteIdeles (a : (InfiniteAdeles K)ˣ) :
    (ideleProductEquiv K (infiniteIdelesInclusion K a)).1 = a := by
  change ((ideleProductEquiv K) ((ideleProductEquiv K).symm (a, 1))).1 = a
  rw [ContinuousMulEquiv.apply_symm_apply]

private theorem infinitePart_finiteInclusion (v : FinitePlace K)
    (a : (FiniteCompletion K v)ˣ) :
    (ideleProductEquiv K (finiteIdeleInclusion K v a)).1 = 1 := by
  apply Units.ext
  rfl

/-- Outside the selected finite places, the inserted local product has value one. -/
theorem finiteIdeleProjection_prescription_of_not_mem
    (v : FinitePlace K) (hv : v ∉ S) (a : PrescriptionLocalProduct K S) :
    finiteIdeleProjection K v (prescriptionIdeleInclusion K S a) = 1 := by
  classical
  change finiteIdeleProjection K v
    (infiniteIdelesInclusion K a.1 * ∏ w : {w // w ∈ S},
      finiteIdeleInclusion K w.1 (a.2 w)) = 1
  rw [map_mul, map_prod, finiteProjection_infiniteIdeles]
  have hne (w : {w // w ∈ S}) : v ≠ w.1 := by
    rintro rfl
    exact hv w.2
  simp only [finiteProjection_finiteInclusion_ne K v _ (hne _),
    Finset.prod_const_one, one_mul]

/-- At a selected finite place, the inserted product has the prescribed coordinate. -/
theorem finiteIdeleProjection_prescription
    (v : {v // v ∈ S}) (a : PrescriptionLocalProduct K S) :
    finiteIdeleProjection K v.1 (prescriptionIdeleInclusion K S a) = a.2 v := by
  classical
  change finiteIdeleProjection K v.1
    (infiniteIdelesInclusion K a.1 * ∏ w : {w // w ∈ S},
      finiteIdeleInclusion K w.1 (a.2 w)) = _
  rw [map_mul, map_prod, finiteProjection_infiniteIdeles, one_mul]
  rw [Finset.prod_eq_single v]
  · exact finiteIdeleProjection_inclusion K v.1 (a.2 v)
  · intro w _ hw
    apply finiteProjection_finiteInclusion_ne
    exact fun h => hw (Subtype.ext h.symm)
  · simp

/-- Inserting the local product and extracting the same coordinates is the identity. -/
theorem prescriptionIdeleRetraction_inclusion (a : PrescriptionLocalProduct K S) :
    prescriptionIdeleRetraction K S (prescriptionIdeleInclusion K S a) = a := by
  classical
  apply Prod.ext
  · change (ideleProductEquiv K
      (infiniteIdelesInclusion K a.1 * ∏ w : {w // w ∈ S},
        finiteIdeleInclusion K w.1 (a.2 w))).1 = a.1
    rw [map_mul, map_prod, Prod.fst_mul, Prod.fst_prod,
      infinitePart_infiniteIdeles]
    simp only [infinitePart_finiteInclusion, Finset.prod_const_one, mul_one]
  · funext v
    exact finiteIdeleProjection_prescription K S v a

@[simp]
theorem finiteIdeleProjection_diagonalUnits (v : FinitePlace K) (a : Kˣ) :
    finiteIdeleProjection K v (diagonalUnits K a) =
      Units.map (algebraMap K (FiniteCompletion K v)).toMonoidHom a := by
  apply Units.ext
  rfl

/-- Almost-everywhere global half-power descent implies the doubled-power
intersection bound on the actual local product and idele-class quotient. -/
theorem prescription_power_preimage_le_of_half_power
    (n : ℕ)
    (hhalf : ∀ a : Kˣ,
      (∀ v : FinitePlace K, v ∉ S →
        ∃ b : (FiniteCompletion K v)ˣ,
          b ^ (2 * n) =
            Units.map (algebraMap K (FiniteCompletion K v)).toMonoidHom a) →
      ∃ b : Kˣ, b ^ n = a) :
    (powMonoidHom (α := IdeleClasses K) (2 * n)).range.comap
        (prescriptionClassMap K S).toMonoidHom ≤
      (powMonoidHom n : PrescriptionLocalProduct K S →*
        PrescriptionLocalProduct K S).range := by
  rintro a ⟨c, hc⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (principalIdeles K) c
  change (ideleClassMap K x) ^ (2 * n) =
    ideleClassMap K (prescriptionIdeleInclusion K S a) at hc
  rw [← map_pow] at hc
  change QuotientGroup.mk' (principalIdeles K) (x ^ (2 * n)) =
    QuotientGroup.mk' (principalIdeles K) (prescriptionIdeleInclusion K S a) at hc
  obtain ⟨z, hz, hxz⟩ :=
    (QuotientGroup.mk'_eq_mk' (principalIdeles K)).mp hc
  obtain ⟨k, rfl⟩ := hz
  have hlocal : ∀ v : FinitePlace K, v ∉ S →
      ∃ b : (FiniteCompletion K v)ˣ,
        b ^ (2 * n) =
          Units.map (algebraMap K (FiniteCompletion K v)).toMonoidHom k := by
    intro v hv
    refine ⟨(finiteIdeleProjection K v x)⁻¹, ?_⟩
    have h := congrArg (finiteIdeleProjection K v) hxz
    rw [map_mul, map_pow, finiteIdeleProjection_diagonalUnits,
      finiteIdeleProjection_prescription_of_not_mem K S v hv] at h
    rw [inv_pow, inv_eq_iff_mul_eq_one]
    exact h
  obtain ⟨b, hb⟩ := hhalf k hlocal
  have hd : (diagonalUnits K b * x ^ 2) ^ n =
      prescriptionIdeleInclusion K S a := by
    rw [mul_pow, ← map_pow (diagonalUnits K), hb, ← pow_mul, mul_comm]
    exact hxz
  refine ⟨prescriptionIdeleRetraction K S (diagonalUnits K b * x ^ 2), ?_⟩
  change (prescriptionIdeleRetraction K S (diagonalUnits K b * x ^ 2)) ^ n = a
  rw [← map_pow, hd, prescriptionIdeleRetraction_inclusion]

end Langlands.Global
