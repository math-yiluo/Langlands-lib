import Langlands.Representation.Classification.RelativeRegularComparisonStatement
import Langlands.Representation.Exponents.ComplexTwistFamilies
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A responsible Weyl branch for strict relative multiplicity excess

An internal, source-derived statement boundary in the continuation argument of
Silberger 1978, Lemma 5.6, printed p.101. This file states branch selection and
its almost-everywhere middle-unitary occurrence; it contains no proof of them.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV uM uW

/-- If the actual ambient Jordan–Hölder multiplicity of the twisted fine
representation strictly exceeds the inner one, one actual fine-Levi-conjugating
permutation outside the coarse Weyl group fixes the real parameter difference
and, for almost every middle unitary parameter, supplies the transported
negative fine twist as a class exponent of the entire middle unitary induction. -/
def GLSupportedRegularMultiplicityBranchObstructionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (Q : BlockRefinement B),
      let D := B.flatten Q
      ∀ (R : BlockRefinement D) (S : BlockRefinement B)
        (h : D.flatten R = B.flatten S)
        (ω : Rep.{uV} ℂ ((D.flatten R).Levi F.Carrier)),
        Representation.IsIrreducible ω.ρ →
        CuspidalSupport.IsLeviCuspidal (D.flatten R) ω.ρ →
        IsUnitarizable ω.ρ →
        ∀ v₀ : Fin (D.flatten R).length → ℝ,
          IsPositiveRootParameter D R v₀ →
          let ωB : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier) := h ▸ ω
          let vB : Fin (B.flatten S).length → ℝ := h ▸ v₀
          ∀ σ : Rep.{uM} ℂ (D.Levi F.Carrier),
            Representation.IsIrreducible σ.ρ → IsLeviSquareIntegrable T D σ →
            (∃ q : (innerInduced T D R (fineTwist T D R ω v₀ 0)).ρ.IntertwiningMap σ.ρ,
              Function.Surjective q) →
            ∀ π : Rep.{uW} ℂ (B.Levi F.Carrier),
              Representation.IsIrreducible π.ρ → IsLeviTempered T B π →
              (∃ q : (middleInduced T B Q σ).ρ.IntertwiningMap π.ρ,
                Function.Surjective q) →
              (∃ q : (innerInduced T B S (fineTwist T B S ωB vB 0)).ρ.IntertwiningMap π.ρ,
                Function.Surjective q) →
              ∀ t : Fin B.length → ℝ, StrictAnti t →
                let τ := fineTwist T B S ωB vB t
                let πt := Rep.of (T.leviRealPowerTwist B t π.ρ)
                ∀ m_in m_amb : ℕ,
                  HasJordanHolderMultiplicity (innerJacquet T B S πt) τ m_in →
                  HasJordanHolderMultiplicity (ambientJacquet T B S πt) τ m_amb →
                  m_in < m_amb →
                  let C := D.flatten R
                  ∃ w : Equiv.Perm (Fin n),
                    ∃ hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) C C w,
                      w ∉ Geometric.blockWeyl B ∧
                      (∀ a : Fin n,
                        v₀ (Geometric.blockIndex C (w.symm a)) -
                            t (Geometric.blockIndex B (w.symm a)) =
                          v₀ (Geometric.blockIndex C a) -
                            t (Geometric.blockIndex B a)) ∧
                      ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin D.length → ℝ)),
                        ComplexTwistFamilies.Occurs T D C C σ w hw ω
                          (ComplexTwistFamilies.unitaryAmbient D)
                          (ComplexTwistFamilies.refinedMixedAffine D R (-v₀)) u

end Langlands
