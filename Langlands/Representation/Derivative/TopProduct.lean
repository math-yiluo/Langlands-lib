import Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof
import Langlands.Representation.Filtration.SingletonIso

/-! The full top derivative of a binary product, naturally in both inputs. -/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Derivative

universe uF uV uW

/-- The sole feasible index at the top derivative order. -/
def topLeibnizIndex (a b : ℕ) : LeibnizIndex a b (a + b) :=
  ⟨(a, b), by simp⟩

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The top-order Leibniz filtration gives an actual natural isomorphism with
the product of the two top derivatives, in every rank. -/
def topProductIso (a b : ℕ) :
    letI := T.topology
    leibnizSource.{uF, uV} T ψ a b (a + b) le_rfl ≅
      leibnizPiece T ψ a b (a + b) (topLeibnizIndex a b) := by
  letI := T.topology
  exact Classical.choice (by
    obtain ⟨e, h⟩ :=
      generalLinearDerivativeLeibnizFiltration.{uF, uV} F T ψ a b (a + b) le_rfl
    exact ⟨h.isoOfLengthOne (by simp) (e (topLeibnizIndex a b)) ≪≫
      eqToIso (congrArg (leibnizPiece T ψ a b (a + b))
        (e.symm_apply_apply (topLeibnizIndex a b)))⟩)

private def rankCastCarrierEquiv {a b : ℕ} (h : a = b)
    (A : letI := T.topology;
      SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    (generalLinearRankCast T h).obj A ≃ₗ[ℂ] A := by
  subst b
  exact LinearEquiv.refl ℂ A

private theorem rankCastCarrierEquiv_naturality {a b : ℕ} (h : a = b)
    {A B : letI := T.topology;
      SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier)}
    (f : letI := T.topology; A ⟶ B)
    (v : letI := T.topology; (generalLinearRankCast T h).obj A) :
    letI := T.topology
    rankCastCarrierEquiv T h B
        (SmoothRep.hom ((generalLinearRankCast T h).map f) v) =
      SmoothRep.hom f (rankCastCarrierEquiv T h A v) := by
  subst b
  rfl

/-- The entire carrier of the top derivative of a binary product is linearly
equivalent to the entire tensor product of the factor top-derivative carriers.
No finite-dimensionality, irreducibility or positive-rank hypothesis is used. -/
def topProductTensorEquiv {a b : ℕ}
    (A : letI := T.topology;
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology;
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    ((generalLinearDerivative T ψ (a + b) (a + b) le_rfl).obj
        ((T.binaryNormalizedProductFunctor a b).obj (A, B))) ≃ₗ[ℂ]
      ((generalLinearDerivative T ψ a a le_rfl).obj A) ⊗[ℂ]
        ((generalLinearDerivative T ψ b b le_rfl).obj B) := by
  letI := T.topology
  exact (Representation.equivOfIso ((topProductIso T ψ a b).app (A, B))).toLinearEquiv
    |>.trans (rankCastCarrierEquiv T
      (leibnizIndices_rank (topLeibnizIndex a b).property) _)
    |>.trans (T.binaryZeroZeroTensorEquiv (Nat.sub_self a) (Nat.sub_self b)
      (((generalLinearDerivative T ψ a a le_rfl).obj A),
        ((generalLinearDerivative T ψ b b le_rfl).obj B))).toLinearEquiv

set_option maxHeartbeats 1200000 in
/-- The full tensor comparison commutes with arbitrary morphisms in both factors. -/
theorem topProductTensorEquiv_naturality {a b : ℕ}
    {A A' : letI := T.topology;
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)}
    {B B' : letI := T.topology;
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; A ⟶ A') (g : letI := T.topology; B ⟶ B')
    (v : letI := T.topology;
      (generalLinearDerivative T ψ (a + b) (a + b) le_rfl).obj
        ((T.binaryNormalizedProductFunctor a b).obj (A, B))) :
    letI := T.topology
    topProductTensorEquiv T ψ A' B'
        (SmoothRep.hom
          ((generalLinearDerivative T ψ (a + b) (a + b) le_rfl).map
            ((T.binaryNormalizedProductFunctor a b).map (f, g))) v) =
      TensorProduct.map
        (SmoothRep.hom ((generalLinearDerivative T ψ a a le_rfl).map f)).toLinearMap
        (SmoothRep.hom ((generalLinearDerivative T ψ b b le_rfl).map g)).toLinearMap
        (topProductTensorEquiv T ψ A B v) := by
  let := T.topology
  have hn :
      ((topProductIso T ψ a b).hom.app (A', B')).hom
          (((leibnizSource T ψ a b (a + b) le_rfl).map (f, g)).hom v) =
        ((leibnizPiece T ψ a b (a + b) (topLeibnizIndex a b)).map (f, g)).hom
          (((topProductIso T ψ a b).hom.app (A, B)).hom v) :=
    congrArg
      (fun (k : (leibnizSource T ψ a b (a + b) le_rfl).obj (A, B) ⟶
          (leibnizPiece T ψ a b (a + b) (topLeibnizIndex a b)).obj (A', B')) =>
        k.hom v)
      ((topProductIso T ψ a b).hom.naturality
        (show (A, B) ⟶ (A', B') from (f, g)))
  change
    T.binaryZeroZeroTensorEquiv (Nat.sub_self a) (Nat.sub_self b) _
        (rankCastCarrierEquiv T (leibnizIndices_rank (topLeibnizIndex a b).property) _
          (((topProductIso T ψ a b).hom.app (A', B')).hom
            (((leibnizSource T ψ a b (a + b) le_rfl).map (f, g)).hom v))) =
      TensorProduct.map _ _
        (T.binaryZeroZeroTensorEquiv (Nat.sub_self a) (Nat.sub_self b) _
          (rankCastCarrierEquiv T (leibnizIndices_rank (topLeibnizIndex a b).property) _
            (((topProductIso T ψ a b).hom.app (A, B)).hom v)))
  rw [hn]
  erw [rankCastCarrierEquiv_naturality]
  exact T.binaryZeroZeroTensorEquiv_naturality (Nat.sub_self a) (Nat.sub_self b)
    (X := (((generalLinearDerivative T ψ a a le_rfl).obj A),
      ((generalLinearDerivative T ψ b b le_rfl).obj B)))
    (Y := (((generalLinearDerivative T ψ a a le_rfl).obj A'),
      ((generalLinearDerivative T ψ b b le_rfl).obj B')))
    (((generalLinearDerivative T ψ a a le_rfl).map f),
      ((generalLinearDerivative T ψ b b le_rfl).map g)) _

end Langlands.Derivative
