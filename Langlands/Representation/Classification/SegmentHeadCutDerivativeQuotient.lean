import Langlands.Representation.Classification.SegmentHeadCutEmbedding
import Langlands.Representation.Classification.SegmentHeadTopDerivative
import Langlands.Representation.Derivative.BinaryTensorInducedQuotient
import Langlands.Representation.Derivative.RankCastCompat
import Langlands.Representation.Induction.BinaryTwoBlockIso
import Langlands.Representation.Tensor.OneFactorQuotient

/-! # Actual quotient maps for consecutive cuts of special-head derivatives -/

noncomputable section

open CategoryTheory

namespace Langlands.Classification.SegmentHeadCut

open GeneralLinear Derivative PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

private def uncastEmbedding {n n' : ℕ} (h : n = n')
    (X : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier))
    (Y : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear n' F.Carrier))
    (j : letI := T.topology
      X.representation.IntertwiningMap ((generalLinearRankCast T h.symm).obj Y).representation)
    (hj : Function.Injective j) :
    letI := T.topology
    {f : ((generalLinearRankCast T h).obj X).representation.IntertwiningMap Y.representation //
      Function.Injective f} := by
  subst h
  exact ⟨j,hj⟩

private theorem rankCast_nontrivial' {n n' : ℕ} (h : n = n')
    (X : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier))
    [Nontrivial X] :
    letI := T.topology
    Nontrivial ((generalLinearRankCast T h).obj X) := by
  let _ := T.topology
  subst h
  change Nontrivial X
  infer_instance

private def derivativeFixedOutputIso
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n n' d k : ℕ} (h : n = n') (hd : d ≤ n) (hd' : d ≤ n')
    (hk : n - d = k) (hk' : n' - d = k) :
    letI := T.topology
    ∀ X : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier),
      ((generalLinearDerivative T ψ n d hd ⋙ generalLinearRankCast T hk).obj X) ≅
        ((generalLinearDerivative T ψ n' d hd' ⋙ generalLinearRankCast T hk').obj
          ((generalLinearRankCast T h).obj X)) := by
  letI := T.topology
  intro X
  let e := Functor.isoWhiskerRight
    (generalLinearRankCastDerivativeIso T ψ h d hd hd') (generalLinearRankCast T hk')
  have e' : (generalLinearDerivative.{uF,uV} T ψ n d hd ⋙
      generalLinearRankCast T (congrArg (fun r => r - d) h)) ⋙
      generalLinearRankCast T hk' ≅
      generalLinearDerivative T ψ n d hd ⋙ generalLinearRankCast T hk := by
    apply eqToIso
    rw [Functor.assoc, generalLinearRankCast_trans]
  exact ((e ≪≫ e').app X).symm

/-- The derivative at a consecutive cut of a supplied long special head
admits an actual surjection onto the supplied upper shorter special head. -/
def headCutDerivativeQuotient
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (ρ : CuspidalDatum.{uV,uF} T)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((a+b)*ρ.rank) F.Carrier)}
    {π₁ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (a*ρ.rank) F.Carrier)}
    {π₂ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (b*ρ.rank) F.Carrier)}
    (hπ : T.IsSegmentHead ⟨ρ,a+b,by omega⟩ π)
    (hπ₁ : T.IsSegmentHead ⟨ρ.twist (b : ℝ),a,ha⟩ π₁)
    (hπ₂ : T.IsSegmentHead ⟨ρ,b,hb⟩ π₂)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) :
    letI := T.topology
    {q : ((generalLinearDerivative T ψ ((a+b)*ρ.rank) (b*ρ.rank)
          (by rw [Nat.add_mul]; exact Nat.le_add_left _ _ : b*ρ.rank ≤ (a+b)*ρ.rank) ⋙
          generalLinearRankCast T (by rw [Nat.add_mul, Nat.add_sub_cancel] : (a+b)*ρ.rank - b*ρ.rank = a*ρ.rank)).obj π)
          ⟶ π₁ // Function.Surjective (SmoothRep.hom q)} := by
  letI := T.topology
  let e := T.binaryNormalizedProductTwoBlockIso
    (Nat.mul_pos ha ρ.rank_pos) (Nat.mul_pos hb ρ.rank_pos) π₁ π₂
  let D₂ := (generalLinearDerivative T ψ (b*ρ.rank) (b*ρ.rank) le_rfl).obj π₂
  letI : Nontrivial D₂ :=
    segmentHeadTopDerivativeNontrivial T ψ ⟨ρ,b,hb⟩ π₂ hπ₂
  letI : Nontrivial ((topDerivative T ψ (b*ρ.rank)).obj π₂) :=
    rankCast_nontrivial' T (Nat.sub_self (b*ρ.rank)) D₂
  let c₀ := BinaryTensor.firstFactorQuotient π₁.representation
    ((topDerivative T ψ (b*ρ.rank)).obj π₂)
  let c : (firstFactorTopDerivative T ψ (a*ρ.rank) (b*ρ.rank)).obj (π₁,π₂) ⟶ π₁ :=
    SmoothRep.ofHom c₀.val
  let P := (T.binaryNormalizedProductFunctor (a*ρ.rank) (b*ρ.rank)).obj (π₁,π₂)
  let h := Nat.add_mul a b ρ.rank
  let X := (generalLinearRankCast T h).obj π
  let j₀ := headCutEmbedding T ρ a b ha hb hπ hπ₁ hπ₂ A hA
  let j₁ := uncastEmbedding T h π P j₀.val j₀.property
  let j : X.representation.IntertwiningMap
      (T.normalizedParabolicInduced
        (Shahidi.twoBlocks (a*ρ.rank) (b*ρ.rank)
          (Nat.mul_pos ha ρ.rank_pos) (Nat.mul_pos hb ρ.rank_pos))
        (binaryLeviTensor T (Nat.mul_pos ha ρ.rank_pos)
          (Nat.mul_pos hb ρ.rank_pos) π₁ π₂).representation) :=
    SmoothRep.hom (SmoothRep.ofHom j₁.val ≫ e.hom)
  have hj : Function.Injective j :=
    (SmoothRep.equivOfIso e).injective.comp j₁.property
  letI := hπ.isIrreducible
  letI : Nontrivial π := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (GeneralLinear ((a+b)*ρ.rank) F.Carrier)) π.representation.asModule
  letI : Nontrivial X := rankCast_nontrivial' T h π
  have hj₀ : j ≠ 0 := by
    intro hz
    obtain ⟨x,hx⟩ := exists_ne (0 : X)
    apply hx
    apply hj
    rw [hz]
    rfl
  let q := binaryTensorDerivativeQuotientOfInducedMap T
    (Nat.mul_pos ha ρ.rank_pos) (Nat.mul_pos hb ρ.rank_pos) ψ
    X π₁ π₂ hπ₁.isIrreducible hπ₂.isIrreducible
    hπ₁.isAdmissible hπ₂.isAdmissible j hj₀
  let E := derivativeFixedOutputIso T ψ h
    (by rw [Nat.add_mul]; exact Nat.le_add_left _ _ : b*ρ.rank ≤ (a+b)*ρ.rank) (Nat.le_add_left (b*ρ.rank) (a*ρ.rank))
    (by rw [Nat.add_mul, Nat.add_sub_cancel] : (a+b)*ρ.rank - b*ρ.rank = a*ρ.rank)
    (Nat.add_sub_cancel (a*ρ.rank) (b*ρ.rank)) π
  refine ⟨E.hom ≫ q.val ≫ c, ?_⟩
  exact c₀.property.comp (q.property.comp (SmoothRep.equivOfIso E).surjective)

end Langlands.Classification.SegmentHeadCut
