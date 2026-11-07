import Langlands.Representation.Classification.SquareIntegrableGenericityStatement
import Langlands.Representation.Classification.SegmentEssentialSquareIntegrableClassificationProof
import Langlands.Representation.Classification.GenericSegmentProductExhaustionProof
import Langlands.Representation.Classification.SegmentProductOrderedAssembly

/-!
# Intrinsic Whittaker genericity of a square-integrable representation

The analytic classification supplies a strong segment head for the original
representation. Its actual singleton normalized induction is isomorphic to
that representation, so the reverse generic-product theorem applies.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Transporting an object to an equal rank and back preserves the object. -/
private def rankCastCancelIso {a b : ℕ} (h : a = b)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    (generalLinearRankCast T h).obj (h.symm ▸ π) ≅ π := by
  subst b
  exact Iso.refl _

/-- Every irreducible analytically square-integrable unitarizable smooth
positive-rank GL representation is generic for every allowed character. -/
theorem squareIntegrableGenericity :
    SquareIntegrableGenericity.{uF,uV} F T := by
  let := T.topology
  intro n π hπi hπsq _hu ψ
  obtain ⟨Δ, hΔ, hhead⟩ :=
    (segmentEssentialSquareIntegrableClassification.{uF,uV} F T
      (n + 1) (Nat.succ_pos n) π hπi).mp hπsq.isEssentiallySquareIntegrable
  let d : SegmentProductDatum.{max uF uV,uF} T (n + 1) :=
    { length := 1
      segments := fun _ => Δ
      degree_sum := by simpa only [Fin.sum_univ_one] using hΔ
      blocks := fun _ => hΔ.symm ▸ π }
  have hd : d.HasSegmentHeads := fun _ => hhead
  have hu : d.multisegment.IsUnlinked := by
    intro Γ hΓ Λ hΛ
    have hΓ' : Γ = Δ := by
      simpa [SegmentProductDatum.multisegment, d] using hΓ
    have hΛ' : Λ = Δ := by
      simpa [SegmentProductDatum.multisegment, d] using hΛ
    subst Γ
    subst Λ
    exact Segment.not_isLinked_self Δ
  have e : d.induced ≅ π :=
    SegmentProductOrderedAssembly.singletonIso d rfl (0 : Fin 1) ≪≫
      rankCastCancelIso F T hΔ π
  exact (genericSegmentProductExhaustion.{uF,uV} T ψ n π).mpr
    ⟨d, hd, hu, ⟨e.symm⟩⟩

end Langlands.Classification
