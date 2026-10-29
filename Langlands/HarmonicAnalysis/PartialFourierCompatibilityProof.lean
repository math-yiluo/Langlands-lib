import Langlands.HarmonicAnalysis.PartialFourierCompatibilityStatement
import Langlands.HarmonicAnalysis.RowFourierCompatibilityProof
import Langlands.HarmonicAnalysis.MatrixFourierSliceProof

/-! Last-column Fourier equivalence from row inversion and column tensors. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

universe uK

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K] {n : ℕ}

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K] in
private theorem pairing_comm (u v : Fin n → K) :
    rowPairing u v = rowPairing v u := by
  exact Finset.sum_congr rfl fun i _ => mul_comm (u i) (v i)

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K] in
private theorem pairing_neg (u v : Fin n → K) :
    rowPairing u (-v) = -rowPairing u v := by
  simp [rowPairing, Finset.sum_neg_distrib]

omit [BorelSpace K] [LocallyCompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K] in
/-- Row closure and the convergent second transform imply convergence for
every row test, without a Borel-space assumption on the product. -/
private theorem row_integrable (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) (hc : RowFourierClosed ψ μ n)
    (hi : IsRowSelfDual ψ μ n) (f : SchwartzBruhat (Fin n → K))
    (y : Fin n → K) :
    Integrable (fun u => ψ.complex (rowPairing u y) * f u) (rowMeasure μ n) := by
  let fneg := Hecke.TestFunction.pullback (Homeomorph.neg (Fin n → K)) f
  obtain ⟨g, hg⟩ := hc fneg
  have hgfun : (g : (Fin n → K) → ℂ) = rowFourierIntegral ψ μ n fneg :=
    funext hg
  have hfg : rowFourierIntegral ψ μ n g = (f : (Fin n → K) → ℂ) := by
    funext u
    rw [hgfun, (hi fneg).2 u]
    simp [fneg]
  simpa only [hfg] using (hi g).1 y

omit [BorelSpace K] [LocallyCompactSpace K] [TotallyDisconnectedSpace K] in
private theorem plus_integrable (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) (hc : RowFourierClosed ψ μ n)
    (hi : IsRowSelfDual ψ μ n)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (m : Matrix (Fin n) (Fin (n + 1)) K) :
    Integrable (fun u => Φ (rectangularJoin (rectangularFirstColumns m) u) *
      ψ.complex (rowPairing (rectangularLastColumn m) u)) (rowMeasure μ n) := by
  have h := row_integrable ψ μ hc hi (rectangularSlice Φ (rectangularFirstColumns m))
    (rectangularLastColumn m)
  simpa only [rectangularSlice_apply, pairing_comm, mul_comm] using h

omit [BorelSpace K] [LocallyCompactSpace K] [TotallyDisconnectedSpace K] in
private theorem minus_integrable (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) (hc : RowFourierClosed ψ μ n)
    (hi : IsRowSelfDual ψ μ n)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (m : Matrix (Fin n) (Fin (n + 1)) K) :
    Integrable (fun u => Φ (rectangularJoin (rectangularFirstColumns m) u) *
      ψ.complex (-rowPairing (rectangularLastColumn m) u)) (rowMeasure μ n) := by
  have h := row_integrable ψ μ hc hi (rectangularSlice Φ (rectangularFirstColumns m))
    (-rectangularLastColumn m)
  simpa only [rectangularSlice_apply, pairing_neg, pairing_comm, mul_comm] using h

private def plusLinear (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) (hc : RowFourierClosed ψ μ n)
    (hi : IsRowSelfDual ψ μ n) :
    SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K) →ₗ[ℂ]
      (Matrix (Fin n) (Fin (n + 1)) K → ℂ) where
  toFun Φ := partialFourierPlusIntegral ψ μ Φ
  map_add' Φ Ψ := by
    ext m
    change (∫ u, (Φ (rectangularJoin (rectangularFirstColumns m) u) +
        Ψ (rectangularJoin (rectangularFirstColumns m) u)) *
        ψ.complex (rowPairing (rectangularLastColumn m) u) ∂rowMeasure μ n) = _
    simp_rw [add_mul]
    exact integral_add (plus_integrable ψ μ hc hi Φ m) (plus_integrable ψ μ hc hi Ψ m)
  map_smul' c Φ := by
    ext m
    change (∫ u, (c * Φ (rectangularJoin (rectangularFirstColumns m) u)) *
        ψ.complex (rowPairing (rectangularLastColumn m) u) ∂rowMeasure μ n) =
      c * ∫ u, Φ (rectangularJoin (rectangularFirstColumns m) u) *
        ψ.complex (rowPairing (rectangularLastColumn m) u) ∂rowMeasure μ n
    simp_rw [mul_assoc]
    exact integral_const_mul c _

omit [MeasurableSpace K] [BorelSpace K] in
private theorem column_decomposition
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
    ∃ (N : ℕ) (c : Fin N → ℂ)
      (g : Fin N → Fin (n + 1) → SchwartzBruhat (Fin n → K)),
      Φ = ∑ j, c j • columnProduct (g j) := by
  let f := Hecke.TestFunction.pullback
    (matrixColumns (K := K) n (n + 1)).toHomeomorph.symm Φ
  obtain ⟨N, c, g, hf⟩ := rowTensorDecomposition (Fin n → K) (n + 1) f
  refine ⟨N, c, g, ?_⟩
  ext m
  have hfm := hf (matrixColumns n (n + 1) m)
  change Φ m = ∑ j, c j * ∏ l, g j l (fun i => m i l) at hfm
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, columnProduct_apply] using hfm

omit [BorelSpace K] [LocallyCompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K] in
private theorem plus_columnProduct (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K)
    (g : Fin (n + 1) → SchwartzBruhat (Fin n → K))
    (m : Matrix (Fin n) (Fin (n + 1)) K) :
    partialFourierPlusIntegral ψ μ (columnProduct g) m =
      (∏ j : Fin n, g j.castSucc (fun i => m i j.castSucc)) *
        rowFourierIntegral ψ μ n (g (Fin.last n)) (rectangularLastColumn m) := by
  unfold partialFourierPlusIntegral
  simp_rw [columnProduct_apply, Fin.prod_univ_castSucc,
    rectangularJoin_castSucc, rectangularJoin_last]
  calc
    (∫ u, ((∏ j : Fin n, g j.castSucc (fun i => rectangularFirstColumns m i j)) *
        g (Fin.last n) u) * ψ.complex (rowPairing (rectangularLastColumn m) u)
        ∂rowMeasure μ n) =
      ∫ u, (∏ j : Fin n, g j.castSucc (fun i => m i j.castSucc)) *
        (ψ.complex (rowPairing u (rectangularLastColumn m)) * g (Fin.last n) u)
        ∂rowMeasure μ n := by
          apply integral_congr_ae
          exact ae_of_all _ fun u => by
            change ((∏ j : Fin n, g j.castSucc (fun i => m i j.castSucc)) *
              g (Fin.last n) u) * ψ.complex (rowPairing (rectangularLastColumn m) u) =
              (∏ j : Fin n, g j.castSucc (fun i => m i j.castSucc)) *
              (ψ.complex (rowPairing u (rectangularLastColumn m)) * g (Fin.last n) u)
            rw [pairing_comm (rectangularLastColumn m)]
            ring
    _ = _ := integral_const_mul _ _

omit [BorelSpace K] in
private theorem plus_closed (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) (hc : RowFourierClosed ψ μ n)
    (hi : IsRowSelfDual ψ μ n)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
    ∃ Ψ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K),
      ∀ m, Ψ m = partialFourierPlusIntegral ψ μ Φ m := by
  classical
  obtain ⟨N, c, g, hΦ⟩ := column_decomposition Φ
  choose k hk using fun j => hc (g j (Fin.last n))
  let q (j : Fin N) := columnProduct (Fin.snoc (fun l => g j l.castSucc) (k j))
  have hq (j : Fin N) (m : Matrix (Fin n) (Fin (n + 1)) K) :
      q j m = partialFourierPlusIntegral ψ μ (columnProduct (g j)) m := by
    rw [plus_columnProduct]
    simp only [q, columnProduct_apply, Fin.prod_univ_castSucc,
      Fin.snoc_castSucc, Fin.snoc_last]
    change (∏ l : Fin n, g j l.castSucc (fun i => m i l.castSucc)) *
      k j (rectangularLastColumn m) = _
    exact congrArg ((∏ l : Fin n, g j l.castSucc (fun i => m i l.castSucc)) * ·)
      (hk j (rectangularLastColumn m))
  refine ⟨∑ j, c j • q j, fun m => ?_⟩
  change (∑ j, c j • q j : SchwartzBruhat _) m = plusLinear ψ μ hc hi Φ m
  rw [hΦ, map_sum]
  simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => congrArg (c j * ·) (hq j m)

private def plusSchwartz (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) (hc : RowFourierClosed ψ μ n)
    (hi : IsRowSelfDual ψ μ n) :
    SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K) →ₗ[ℂ]
      SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K) :=
  (plusLinear ψ μ hc hi).codRestrict _ fun Φ => by
    obtain ⟨Ψ, hΨ⟩ := plus_closed ψ μ hc hi Φ
    have he : plusLinear ψ μ hc hi Φ =
        (Ψ : Matrix (Fin n) (Fin (n + 1)) K → ℂ) :=
      funext fun m => (hΨ m).symm
    rw [he]
    exact Ψ.property

omit [IsTopologicalRing K] [BorelSpace K] [LocallyCompactSpace K]
  [TotallyDisconnectedSpace K] in
private theorem plus_eq_slice (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (m : Matrix (Fin n) (Fin (n + 1)) K) :
    partialFourierPlusIntegral ψ μ Φ m =
      rowFourierIntegral ψ μ n (rectangularSlice Φ (rectangularFirstColumns m))
        (rectangularLastColumn m) := by
  unfold partialFourierPlusIntegral rowFourierIntegral
  apply integral_congr_ae
  exact ae_of_all _ fun u => by
    change Φ (rectangularJoin (rectangularFirstColumns m) u) *
      ψ.complex (rowPairing (rectangularLastColumn m) u) =
      ψ.complex (rowPairing u (rectangularLastColumn m)) *
        Φ (rectangularJoin (rectangularFirstColumns m) u)
    rw [pairing_comm (rectangularLastColumn m), mul_comm]

omit [BorelSpace K] in
private theorem plusSchwartz_twice (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) (hc : RowFourierClosed ψ μ n)
    (hi : IsRowSelfDual ψ μ n)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (m : Matrix (Fin n) (Fin (n + 1)) K) :
    plusSchwartz ψ μ hc hi (plusSchwartz ψ μ hc hi Φ) m =
      Φ (rectangularJoin (rectangularFirstColumns m) (-rectangularLastColumn m)) := by
  change partialFourierPlusIntegral ψ μ (plusSchwartz ψ μ hc hi Φ) m = _
  rw [plus_eq_slice]
  have hs : (rectangularSlice (plusSchwartz ψ μ hc hi Φ) (rectangularFirstColumns m) :
      (Fin n → K) → ℂ) =
      rowFourierIntegral ψ μ n (rectangularSlice Φ (rectangularFirstColumns m)) := by
    funext u
    change partialFourierPlusIntegral ψ μ Φ
      (rectangularJoin (rectangularFirstColumns m) u) = _
    rw [plus_eq_slice]
    simp only [rectangularFirstColumns_join, rectangularLastColumn_join]
  rw [hs, (hi (rectangularSlice Φ (rectangularFirstColumns m))).2]
  rfl

omit [BorelSpace K] in
private theorem plusSchwartz_fourth (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) (hc : RowFourierClosed ψ μ n)
    (hi : IsRowSelfDual ψ μ n)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
    plusSchwartz ψ μ hc hi (plusSchwartz ψ μ hc hi
      (plusSchwartz ψ μ hc hi (plusSchwartz ψ μ hc hi Φ))) = Φ := by
  ext m
  rw [plusSchwartz_twice, plusSchwartz_twice]
  simp only [rectangularFirstColumns_join, rectangularLastColumn_join, neg_neg,
    rectangularJoin_split]

omit [IsTopologicalRing K] [BorelSpace K] [LocallyCompactSpace K]
  [T2Space K] [TotallyDisconnectedSpace K] in
private theorem plus_reflect (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (m : Matrix (Fin n) (Fin (n + 1)) K) :
    partialFourierPlusIntegral ψ μ Φ
        (rectangularJoin (rectangularFirstColumns m) (-rectangularLastColumn m)) =
      partialFourierIntegral ψ μ Φ m := by
  simp only [partialFourierPlusIntegral, partialFourierIntegral,
    rectangularFirstColumns_join, rectangularLastColumn_join]
  apply integral_congr_ae
  exact ae_of_all _ fun u => by
    change Φ (rectangularJoin (rectangularFirstColumns m) u) *
      ψ.complex (rowPairing (-rectangularLastColumn m) u) =
      Φ (rectangularJoin (rectangularFirstColumns m) u) *
        ψ.complex (-rowPairing (rectangularLastColumn m) u)
    rw [pairing_comm (-rectangularLastColumn m), pairing_neg, pairing_comm u]

/-- The inverse-character last-column transform and its plus-character inverse
form an equivalence of the whole Schwartz space, with both integrals convergent. -/
theorem partialFourierCompatibility : PartialFourierCompatibilityStatement.{uK} := by
  intro K _ _ _ _ _ _ _ _ ψ μ n hself
  obtain ⟨hc, hi⟩ := rowFourierCompatibility ψ μ n hself
  let P := plusSchwartz ψ μ hc hi
  let T : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K) ≃ₗ[ℂ]
      SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K) :=
    { toLinearMap := P.comp (P.comp P)
      invFun := P
      left_inv := fun Φ => plusSchwartz_fourth ψ μ hc hi Φ
      right_inv := fun Φ => plusSchwartz_fourth ψ μ hc hi Φ }
  refine ⟨T, ?_, ?_, minus_integrable ψ μ hc hi, plus_integrable ψ μ hc hi⟩
  · intro Φ m
    change plusSchwartz ψ μ hc hi
      (plusSchwartz ψ μ hc hi (plusSchwartz ψ μ hc hi Φ)) m = _
    rw [plusSchwartz_twice]
    exact plus_reflect ψ μ Φ m
  · intro Φ m
    rfl

end Langlands.HarmonicAnalysis
