import Langlands.HarmonicAnalysis.TwoBlockRowFourierCompanionStatement
import Langlands.HarmonicAnalysis.TwoBlockRowPartialFourierData
import Langlands.HarmonicAnalysis.RowFourierCompatibilityProof
import Langlands.HarmonicAnalysis.PadicRowFourierEquivarianceProof
import Langlands.HarmonicAnalysis.ScalarFourierClosureProof
import Langlands.LocalField.Normalization.Proof
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Proof of the two-block row Fourier companion identity

The arbitrary-row form of JPSS 1983, (4.8.3), is reduced by full-row Fourier
equivariance under `weylLong * g` and the coordinate reversal of the second block to
a partial Fourier inversion in the first `b` coordinates of the swapped row. That
inversion is proved on joined tensors, using the product decomposition of the row
measure and row Fourier inversion in dimension `b`.
-/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis

open TwoBlockRowPartialFourier

namespace TwoBlockRowFourierCompanion

section Measure

variable {K : Type*} [MeasurableSpace K] {a b N : ℕ}

/-- The block join `(u, v) ↦ join e u v` as a measurable equivalence. -/
def joinMeasurableEquiv (e : Fin b ⊕ Fin a ≃ Fin N) :
    ((Fin b → K) × (Fin a → K)) ≃ᵐ (Fin N → K) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin b ⊕ Fin a => K)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin N => K) e)

theorem joinMeasurableEquiv_apply (e : Fin b ⊕ Fin a ≃ Fin N)
    (p : (Fin b → K) × (Fin a → K)) : joinMeasurableEquiv e p = join e p.1 p.2 := by
  funext j
  obtain ⟨s, rfl⟩ := e.surjective j
  simp only [joinMeasurableEquiv, MeasurableEquiv.trans_apply]
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  cases s <;> simp [MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi]

end Measure

section General

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] {a b N : ℕ}

omit [IsTopologicalRing K] [BorelSpace K] in
/-- The product of the two block row measures is carried to the full row measure. -/
theorem measurePreserving_joinMeasurableEquiv (μ : AdditiveHaarMeasure K)
    [SigmaFinite μ.measure] (e : Fin b ⊕ Fin a ≃ Fin N) :
    MeasurePreserving (joinMeasurableEquiv (K := K) e)
      ((rowMeasure μ b).prod (rowMeasure μ a)) (rowMeasure μ N) :=
  (measurePreserving_piCongrLeft (fun _ : Fin N => μ.measure) e).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin b ⊕ Fin a => μ.measure))

omit [IsTopologicalRing K] [BorelSpace K] in
/-- Reversing the coordinates of a row preserves the row measure. -/
theorem integral_comp_rev (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure] {d : ℕ}
    (f : (Fin d → K) → ℂ) :
    ∫ w, f (w ∘ Fin.rev) ∂rowMeasure μ d = ∫ v, f v ∂rowMeasure μ d := by
  have h := measurePreserving_arrowCongr' (fun _ : Fin d => μ.measure)
    (fun _ : Fin d => μ.measure) Fin.revPerm (MeasurableEquiv.refl K)
    fun _ => MeasurePreserving.id _
  exact h.integral_comp' f

omit [IsTopologicalRing K] [BorelSpace K] in
/-- The full-row Fourier integral of a joined tensor at a joined point is the product of
the block Fourier integrals. -/
theorem rowFourierIntegral_joinedTensor_join [T2Space K] (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure] (e : Fin b ⊕ Fin a ≃ Fin N)
    (α : SchwartzBruhat (Fin b → K)) (β : SchwartzBruhat (Fin a → K))
    (u : Fin b → K) (η : Fin a → K) :
    rowFourierIntegral ψ μ N (joinedTensor e α β) (join e u η) =
      rowFourierIntegral ψ μ b α u * rowFourierIntegral ψ μ a β η := by
  unfold rowFourierIntegral
  rw [← (measurePreserving_joinMeasurableEquiv μ e).integral_comp']
  simp only [joinMeasurableEquiv_apply, rowPairing_join, joinedTensor_join,
    AddChar.map_add_eq_mul]
  rw [← integral_prod_mul]
  congr 1
  funext q
  ring

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K] in
/-- The row pairing is additive, hence odd, in its second argument. -/
theorem rowPairing_neg_right {d : ℕ} (x y : Fin d → K) :
    rowPairing x (-y) = -rowPairing x y := by
  simp [rowPairing, Finset.sum_neg_distrib]

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K] in
/-- Reversing the coordinates of the first argument of the row pairing is the same as
reversing those of the second. -/
theorem rowPairing_comp_rev {d : ℕ} (x y : Fin d → K) :
    rowPairing (x ∘ Fin.rev) y = rowPairing x (y ∘ Fin.rev) := by
  unfold rowPairing
  exact Fintype.sum_equiv Fin.revPerm _ _ fun i => by simp

variable [T2Space K] [LocallyCompactSpace K] [TotallyDisconnectedSpace K]

/-- Partial Fourier inversion in the first block: for a full-row Fourier pair, the
inverse-character transform of `Ψhat` in the first block, with the second block fixed at
`η`, is the plus-character transform of `Ψ` in the second block, with the first block fixed
at `ξ`, evaluated at `η`. -/
theorem integral_join_rowFourierPair (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure] (hrow : IsRowSelfDual ψ μ b)
    (e : Fin b ⊕ Fin a ≃ Fin N) (Ψ Ψhat : SchwartzBruhat (Fin N → K))
    (hΨ : IsRowFourierPair ψ μ Ψ Ψhat) (ξ : Fin b → K) (η : Fin a → K) :
    ∫ u, ψ.complex (-rowPairing u ξ) * Ψhat (join e u η) ∂rowMeasure μ b =
      ∫ v, ψ.complex (rowPairing v η) * Ψ (join e ξ v) ∂rowMeasure μ a := by
  obtain ⟨M, α, β, hΨeq⟩ := exists_joinedTensor_expansion e Ψ
  have hsum (z : Fin N → K) : Ψ z = ∑ j, joinedTensor e (α j) (β j) z := by
    rw [hΨeq]
    simp [Finset.sum_apply]
  have hval (z : Fin N → K) : Ψ z = ∑ j, α j (first e z) * β j (second e z) := by
    simp [hsum]
  have hhat (u : Fin b → K) : Ψhat (join e u η) =
      ∑ j, rowFourierIntegral ψ μ b (α j) u * rowFourierIntegral ψ μ a (β j) η := by
    rw [hΨ]
    calc rowFourierIntegral ψ μ N Ψ (join e u η)
        = ∑ j, rowFourierIntegral ψ μ N (joinedTensor e (α j) (β j)) (join e u η) := by
          simp only [rowFourierIntegral, hsum, Finset.mul_sum]
          exact integral_finsetSum _ fun j _ =>
            schwartz_rowFourierIntegrand_integrable ψ μ (joinedTensor e (α j) (β j)) _
      _ = _ := Finset.sum_congr rfl fun j _ =>
          rowFourierIntegral_joinedTensor_join ψ μ e (α j) (β j) u η
  calc ∫ u, ψ.complex (-rowPairing u ξ) * Ψhat (join e u η) ∂rowMeasure μ b
      = ∫ u, ∑ j, (ψ.complex (rowPairing u (-ξ)) * rowFourierIntegral ψ μ b (α j) u) *
          rowFourierIntegral ψ μ a (β j) η ∂rowMeasure μ b := by
        congr 1
        funext u
        rw [hhat, rowPairing_neg_right, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j, (∫ u, ψ.complex (rowPairing u (-ξ)) * rowFourierIntegral ψ μ b (α j) u
          ∂rowMeasure μ b) * rowFourierIntegral ψ μ a (β j) η := by
        rw [integral_finsetSum]
        · exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
        · exact fun j _ => ((hrow (α j)).1 (-ξ)).mul_const _
    _ = ∑ j, α j ξ * rowFourierIntegral ψ μ a (β j) η := by
        refine Finset.sum_congr rfl fun j _ => ?_
        change rowFourierIntegral ψ μ b (rowFourierIntegral ψ μ b (α j)) (-ξ) * _ = _
        rw [(hrow (α j)).2, neg_neg]
    _ = ∫ v, ∑ j, α j ξ * (ψ.complex (rowPairing v η) * β j v) ∂rowMeasure μ a := by
        rw [integral_finsetSum]
        · exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
        · exact fun j _ => (schwartz_rowFourierIntegrand_integrable ψ μ (β j) η).const_mul _
    _ = ∫ v, ψ.complex (rowPairing v η) * Ψ (join e ξ v) ∂rowMeasure μ a := by
        congr 1
        funext v
        rw [hval, first_join, second_join, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring

end General

section Coordinates

variable {R : Type*} {a b : ℕ}

/-- The swapped row is the join for the placement of the `b` block first. -/
theorem twoBlockSwappedRow_eq_join (u : Fin b → R) (v : Fin a → R) :
    twoBlockSwappedRow u v = join (contiguousEquiv (Nat.add_comm b a)) u v := by
  rw [join_contiguousEquiv]
  rfl

/-- Reversing the swapped row `(ξ, w ∘ rev)` gives the ordinary row `(w, ξ ∘ rev)`. -/
theorem twoBlockSwappedRow_comp_rev (ξ : Fin b → R) (w : Fin a → R) :
    twoBlockSwappedRow ξ (w ∘ Fin.rev) ∘ Fin.rev = Fin.append w (ξ ∘ Fin.rev) := by
  funext j
  simp only [Function.comp_apply, twoBlockSwappedRow, finCongr_apply, Fin.cast_rev,
    Fin.append_rev]
  simp [Function.comp_def]

end Coordinates

section Weyl

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Right multiplication by the long Weyl element reverses the coordinates of a row. -/
theorem vecMul_weylLong (x : Fin n → R) :
    Matrix.vecMul x (Langlands.GeneralLinear.weylLong n R).val = x ∘ Fin.rev := by
  funext j
  simp [Matrix.vecMul, dotProduct, Langlands.GeneralLinear.weylLong_entry]

end Weyl

end TwoBlockRowFourierCompanion

open TwoBlockRowFourierCompanion

universe uF

/-- The two-block row Fourier companion identity, JPSS 1983, (4.8.3), with arbitrary
fixed rows. -/
theorem twoBlockRowFourierCompanion : TwoBlockRowFourierCompanionStatement.{uF} := by
  intro p _ F
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  have : TotallyDisconnectedSpace F.Carrier := by
    let : NonarchimedeanRing F.Carrier := by
      convert! ValuativeRel.nonarchimedeanRing F.Carrier
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  intro ψ μ hsd a b _ _
  obtain ⟨hσ, -⟩ := scalarFourierClosure F.Carrier ψ μ hsd
  have hcompat (d : ℕ) := rowFourierCompatibility ψ μ d hsd
  refine ⟨(hcompat (a + b)).1, ?_⟩
  intro Φ Φhat hpair g ξ η
  let T := F.canonicalTopologicalData
  let W := Langlands.GeneralLinear.weylLong (a + b) F.Carrier
  let e : Fin b ⊕ Fin a ≃ Fin (a + b) := contiguousEquiv (Nat.add_comm b a)
  let e' : Fin a ⊕ Fin b ≃ Fin (a + b) := contiguousEquiv rfl
  -- `Ψ = Φ (· (W g))` and `Φg = Φ (· g)` are test functions; `Ψhat` is the Fourier
  -- transform of `Ψ`.
  obtain ⟨⟨Ψ, hΨ⟩, hΨfour⟩ := padicRowFourierEquivariance F T (a + b) ψ μ (W * g) Φ
  obtain ⟨⟨Φg, hΦg⟩, -⟩ := padicRowFourierEquivariance F T (a + b) ψ μ g Φ
  obtain ⟨Ψhat, hΨhat⟩ := (hcompat (a + b)).1 Ψ
  -- `|det (W g)| = |det g| ≠ 0`.
  have hW : T.normalizedAbs (Matrix.det W.val) = 1 := by
    have h1 : Matrix.det W.val * Matrix.det W.val = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, Langlands.GeneralLinear.weylLong_mul_self,
        Units.val_one, Matrix.det_one]
    have h2 := congrArg T.normalizedAbs h1
    rw [T.normalizedAbs_mul, T.normalizedAbs_one] at h2
    nlinarith [T.normalizedAbs_nonneg (Matrix.det W.val)]
  have hdet :
      T.normalizedAbs (Matrix.det (W * g).val) = T.normalizedAbs (Matrix.det g.val) := by
    rw [Units.val_mul, Matrix.det_mul, T.normalizedAbs_mul, hW, one_mul]
  have hdetg : Matrix.det g.val ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det g.val).mp g.isUnit).ne_zero
  have hc0 : (T.normalizedAbs (Matrix.det g.val) : ℂ) ≠ 0 := by
    exact_mod_cast (T.normalizedAbs_pos hdetg).ne'
  have hM : ((W * g)⁻¹).val.transpose =
      (W * Langlands.GeneralLinear.inverseTranspose (a + b) F.Carrier g).val := by
    rw [← Langlands.GeneralLinear.inverseTranspose_coe, map_mul,
      Langlands.GeneralLinear.inverseTranspose_weylLong]
  -- The left integrand is `|det g|` times the inverse-character integrand of `Ψhat`.
  have hΦhat (y : Fin (a + b) → F.Carrier) :
      Φhat (Matrix.vecMul y
        (W * Langlands.GeneralLinear.inverseTranspose (a + b) F.Carrier g).val) =
        (T.normalizedAbs (Matrix.det g.val) : ℂ) * Ψhat y := by
    rw [hΨhat y, hΨfour Ψ hΨ y, hdet, hM, ← hpair, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  have hLfun : (fun u : Fin b → F.Carrier =>
      ψ.complex (-rowPairing u ξ) *
        Φhat (Matrix.vecMul (twoBlockSwappedRow u η)
          (W * Langlands.GeneralLinear.inverseTranspose (a + b) F.Carrier g).val)) =
      fun u => (T.normalizedAbs (Matrix.det g.val) : ℂ) *
        (ψ.complex (rowPairing u (-ξ)) * slice e Ψhat η u) := by
    funext u
    rw [hΦhat, slice_apply, twoBlockSwappedRow_eq_join, rowPairing_neg_right]
    ring
  -- The right integrand is the Fourier integrand of a slice of `Φg`.
  have hRfun : (fun w : Fin a → F.Carrier =>
      ψ.complex (rowPairing w (η ∘ Fin.rev)) *
        Φ (Matrix.vecMul (Fin.append w (ξ ∘ Fin.rev)) g.val)) =
      fun w => ψ.complex (rowPairing w (η ∘ Fin.rev)) * slice e' Φg (ξ ∘ Fin.rev) w := by
    funext w
    rw [slice_apply, hΦg, join_contiguousEquiv]
    rfl
  -- After the reversal `v = w ∘ rev`, the right integrand is the plus-character
  -- integrand of `Ψ` in the second block of the swapped row.
  have hΨrev (w : Fin a → F.Carrier) :
      ψ.complex (rowPairing (w ∘ Fin.rev) η) * Ψ (join e ξ (w ∘ Fin.rev)) =
        ψ.complex (rowPairing w (η ∘ Fin.rev)) *
          Φ (Matrix.vecMul (Fin.append w (ξ ∘ Fin.rev)) g.val) := by
    rw [rowPairing_comp_rev, hΨ, Units.val_mul, ← Matrix.vecMul_vecMul,
      ← twoBlockSwappedRow_eq_join, vecMul_weylLong, twoBlockSwappedRow_comp_rev]
  refine ⟨?_, ?_, ?_⟩
  · rw [hLfun]
    exact (schwartz_rowFourierIntegrand_integrable ψ μ (slice e Ψhat η) (-ξ)).const_mul _
  · rw [hRfun]
    exact schwartz_rowFourierIntegrand_integrable ψ μ (slice e' Φg (ξ ∘ Fin.rev)) (η ∘ Fin.rev)
  · rw [hLfun, integral_const_mul, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    simp only [slice_apply, rowPairing_neg_right]
    rw [integral_join_rowFourierPair ψ μ (hcompat b).2 e Ψ Ψhat hΨhat ξ η]
    refine (integral_comp_rev μ
      (fun v => ψ.complex (rowPairing v η) * Ψ (join e ξ v))).symm.trans ?_
    exact integral_congr_ae (Filter.Eventually.of_forall hΨrev)

end Langlands.HarmonicAnalysis
