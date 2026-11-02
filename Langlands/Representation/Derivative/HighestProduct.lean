import Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof
import Langlands.Representation.Derivative.ProductVanishing
import Langlands.Representation.Filtration.SingleSurvivingGrade

/-! Highest derivative bounds and the actual single-survivor isomorphism. -/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.HighestProduct

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

private theorem subsingleton_rankCast {a b : ℕ} (h : a = b)
    (A : letI := T.topology;
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (hA : Subsingleton A) :
    let _ := T.topology
    Subsingleton ((generalLinearRankCast T h).obj A) := by
  subst b
  exact hA

variable {a b : ℕ}
  (A : letI := T.topology;
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
  (B : letI := T.topology;
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
  (r s : ℕ) (hr : r ≤ a) (hs : s ≤ b)
  (hA : ∀ j (hj : j ≤ a), r < j →
    Subsingleton ((generalLinearDerivative T ψ a j hj).obj A))
  (hB : ∀ j (hj : j ≤ b), s < j →
    Subsingleton ((generalLinearDerivative T ψ b j hj).obj B))

include hA hB in
private theorem subsingleton_piece {d : ℕ} (x : LeibnizIndex a b d)
    (hx : r < x.val.1 ∨ s < x.val.2) :
    let _ := T.topology
    Subsingleton ((leibnizPiece T ψ a b d x).obj (A, B)) := by
  let _ := T.topology
  apply subsingleton_rankCast
  apply ProductVanishing.subsingleton_binary
  rcases hx with hx | hx
  · exact Or.inl (hA _ _ hx)
  · exact Or.inr (hB _ _ hx)

include hA hB in
/-- A binary product has no derivative above the sum of two factor bounds. -/
theorem subsingleton_above (d : ℕ) (hd : d ≤ a + b) (hlt : r + s < d) :
    let _ := T.topology
    Subsingleton ((generalLinearDerivative T ψ (a + b) d hd).obj
      ((T.binaryNormalizedProductFunctor a b).obj (A, B))) := by
  let _ := T.topology
  obtain ⟨e, t, ht⟩ :=
    GeneralLinearDerivativeLeibnizFiltrationStatement.filtration T
      (generalLinearDerivativeLeibnizFiltration.{uF, uV} F T) ψ a b d hd
  apply t.subsingleton_atObject (A, B)
  intro i
  obtain ⟨E⟩ := ht i
  have hxsum := leibnizIndices_sum (e.symm i).property
  have hx : r < (e.symm i).val.1 ∨ s < (e.symm i).val.2 := by omega
  let _ := subsingleton_piece T ψ A B r s hA hB (e.symm i) hx
  exact (Representation.equivOfIso (E.app (A, B))).toEquiv.injective.subsingleton

include hA hB in
/-- At the sum of factor bounds the actual derivative is isomorphic to the
rank-transported binary product of the two derivatives at those bounds.
The factors and the surviving quotient may be zero. -/
theorem highestIso (hrs : r + s ≤ a + b) :
    let _ := T.topology
    Nonempty (((generalLinearDerivative T ψ (a + b) (r + s) hrs).obj
      ((T.binaryNormalizedProductFunctor a b).obj (A, B))) ≅
      (generalLinearRankCast T (by omega : (a - r) + (b - s) = (a + b) - (r + s))).obj
        ((T.binaryNormalizedProductFunctor (a - r) (b - s)).obj
          ((generalLinearDerivative T ψ a r hr).obj A,
            (generalLinearDerivative T ψ b s hs).obj B))) := by
  let _ := T.topology
  let x₀ : LeibnizIndex a b (r + s) :=
    ⟨(r, s), mem_leibnizIndices.mpr ⟨hr, hs, rfl⟩⟩
  obtain ⟨e, t, ht⟩ :=
    GeneralLinearDerivativeLeibnizFiltrationStatement.filtration T
      (generalLinearDerivativeLeibnizFiltration.{uF, uV} F T) ψ a b (r + s) hrs
  have hzero : ∀ i, i ≠ e x₀ → Subsingleton ((t.graded i).obj (A, B)) := by
    intro i hi
    obtain ⟨E⟩ := ht i
    have hxsum := leibnizIndices_sum (e.symm i).property
    have hxne : e.symm i ≠ x₀ := by
      intro h
      apply hi
      simpa using congrArg e h
    have hx : r < (e.symm i).val.1 ∨ s < (e.symm i).val.2 := by
      by_contra h
      have hfirst : (e.symm i).val.1 = r := by omega
      have hsecond : (e.symm i).val.2 = s := by omega
      exact hxne (Subtype.ext (Prod.ext hfirst hsecond))
    let _ := subsingleton_piece T ψ A B r s hA hB (e.symm i) hx
    exact (Representation.equivOfIso (E.app (A, B))).toEquiv.injective.subsingleton
  obtain ⟨E⟩ := ht (e x₀)
  let q : (leibnizSource T ψ a b (r + s) hrs).obj (A, B) ≅
      (leibnizPiece T ψ a b (r + s) x₀).obj (A, B) :=
    t.singleSurvivingGradeIsoAt (A, B) (e x₀) hzero ≪≫
      E.app (A, B) ≪≫
      eqToIso (congrArg (fun x => (leibnizPiece T ψ a b (r + s) x).obj (A, B))
        (e.symm_apply_apply x₀))
  exact ⟨SmoothRep.mkIso (Representation.equivOfIso q)⟩

include hA hB in
/-- Choose the actual highest-product isomorphism from the single surviving grade. -/
def highestProductIso (hrs : r + s ≤ a + b) :
    letI := T.topology
    ((generalLinearDerivative T ψ (a + b) (r + s) hrs).obj
      ((T.binaryNormalizedProductFunctor a b).obj (A, B))) ≅
      (generalLinearRankCast T (by omega : (a - r) + (b - s) = (a + b) - (r + s))).obj
        ((T.binaryNormalizedProductFunctor (a - r) (b - s)).obj
          ((generalLinearDerivative T ψ a r hr).obj A,
            (generalLinearDerivative T ψ b s hs).obj B)) :=
  Classical.choice (highestIso T ψ A B r s hr hs hA hB hrs)

end Langlands.Derivative.HighestProduct
