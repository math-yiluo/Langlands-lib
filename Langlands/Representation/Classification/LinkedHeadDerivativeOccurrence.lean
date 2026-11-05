import Langlands.Representation.Classification.LinkedSegmentTerminalWitness
import Langlands.Representation.Classification.SegmentHeadCutDerivativeQuotient
import Langlands.Representation.Derivative.LeibnizQuotientOccurrence

/-! Actual quotient occurrences for terminal cuts of supplied special heads. -/

noncomputable section

open CategoryTheory

namespace Langlands.Classification

open GeneralLinear Derivative PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

private def zeroDerivativeFixedRankIso
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (n k : ℕ) (hk : k = 0) (hle : k ≤ n) (hout : n-k = n)
    (X : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)) :
    letI := T.topology
    ((generalLinearDerivative T ψ n k hle ⋙ generalLinearRankCast T hout).obj X) ≅ X := by
  subst k
  exact Iso.refl _

/-- Include the zero cut in the actual quotient construction. -/
def headCutDerivativeQuotientIncludingZero
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (ρ : CuspidalDatum.{uV,uF} T) (a b : ℕ) (ha : 0 < a)
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((a+b)*ρ.rank) F.Carrier)}
    {H : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (a*ρ.rank) F.Carrier)}
    (hπ : T.IsSegmentHead ⟨ρ,a+b,by omega⟩ π)
    (hH : T.IsSegmentHead ⟨ρ.twist (b : ℝ),a,ha⟩ H) :
    letI := T.topology
    {q : ((generalLinearDerivative T ψ ((a+b)*ρ.rank) (b*ρ.rank)
          (by rw [Nat.add_mul]; exact Nat.le_add_left _ _ : b*ρ.rank ≤ (a+b)*ρ.rank) ⋙
          generalLinearRankCast T (by rw [Nat.add_mul, Nat.add_sub_cancel] :
            (a+b)*ρ.rank - b*ρ.rank = a*ρ.rank)).obj π) ⟶ H //
      Function.Surjective (SmoothRep.hom q)} := by
  letI := T.topology
  apply Classical.choice
  cases b with
  | zero =>
    have hH' : T.IsSegmentHead ⟨ρ,a,ha⟩ H := by
      obtain ⟨A,hA,hhead⟩ := hH
      refine ⟨A,?_,hhead⟩
      simpa only [CuspidalDatum.IsRepresentedBy, CuspidalDatum.twist,
        Nat.cast_zero, T.supercuspidalClassRealPowerTwist_zero] using hA
    obtain ⟨A,hA,hπA⟩ := hπ
    obtain ⟨e⟩ := hπA.nonempty_headEquiv
    obtain ⟨eH⟩ := ((T.isSegmentHead_iff ⟨ρ,a,ha⟩ H A hA).mp hH').nonempty_headEquiv
    let E := SmoothRep.mkIso (e.symm.trans eH)
    let Z := zeroDerivativeFixedRankIso T ψ ((a+0)*ρ.rank) (0*ρ.rank)
      (Nat.zero_mul _) (by omega) (by simp) π
    exact ⟨⟨Z.hom ≫ E.hom,(SmoothRep.hom_hom_surjective E).comp
      (SmoothRep.hom_hom_surjective Z)⟩⟩
  | succ b =>
    obtain ⟨L,hL,-⟩ := segmentSpecialConstituentExistence F T
      (⟨ρ,b+1,Nat.zero_lt_succ b⟩ : Segment.{uV,uF} T)
    have hex := hπ
    obtain ⟨A,hA,-⟩ := hex
    exact ⟨SegmentHeadCut.headCutDerivativeQuotient T ψ ρ a (b+1) ha
      (Nat.zero_lt_succ b) hπ hH hL A hA⟩

/-- A supplied terminal head is an actual quotient of the corresponding
rank-cast derivative of a supplied long head, including cut zero. -/
def headTerminalDerivativeQuotient
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (Δ E : Segment.{uV,uF} T) (c : ℕ)
    (hbase : E.base = Δ.base.twist (c : ℝ))
    (hlen : E.length + c = Δ.length)
    (hr : c*Δ.rank ≤ Δ.degree) (hd : Δ.degree - c*Δ.rank = E.degree)
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    {H : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear E.degree F.Carrier)}
    (hπ : T.IsSegmentHead Δ π) (hH : T.IsSegmentHead E H) :
    letI := T.topology
    {q : ((generalLinearDerivative T ψ Δ.degree (c*Δ.rank) hr ⋙
      generalLinearRankCast T hd).obj π) ⟶ H //
      Function.Surjective (SmoothRep.hom q)} := by
  cases Δ with
  | mk ρ l hl =>
    cases E with
    | mk σ a ha =>
      change σ = ρ.twist (c : ℝ) at hbase
      subst σ
      change a+c = l at hlen
      subst l
      exact headCutDerivativeQuotientIncludingZero T ψ ρ a c ha hπ hH

private theorem witness_rank
    {Δ Γ U : Segment.{uV,uF} T} {I : Option (Segment.{uV,uF} T)}
    (w : Segment.LinkedTerminalWitness Δ Γ U I) : w.segment.rank = Δ.rank := by
  have h := congrArg CuspidalDatum.rank w.base_eq
  exact h

private theorem witness_cut_rank_le
    {Δ Γ U : Segment.{uV,uF} T} {I : Option (Segment.{uV,uF} T)}
    (w : Segment.LinkedTerminalWitness Δ Γ U I) : w.cut*Δ.rank ≤ Δ.degree :=
  Nat.mul_le_mul_right Δ.rank (Nat.le_of_lt w.cut_lt)

private theorem witness_residual_rank
    {Δ Γ U : Segment.{uV,uF} T} {I : Option (Segment.{uV,uF} T)}
    (w : Segment.LinkedTerminalWitness Δ Γ U I) :
    Δ.degree - w.cut*Δ.rank = w.segment.degree := by
  change Δ.length*Δ.rank - w.cut*Δ.rank = w.segment.length*w.segment.rank
  rw [witness_rank T w, ← w.length_add_cut, Nat.add_mul, Nat.add_sub_cancel]

private theorem rankCast_surjective {m n : ℕ} (h : m = n)
    {A B : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (q : letI := T.topology; A ⟶ B)
    (hq : letI := T.topology; Function.Surjective (SmoothRep.hom q)) :
    letI := T.topology
    Function.Surjective (SmoothRep.hom ((generalLinearRankCast T h).map q)) := by
  subst n
  exact hq

/-- The actual residual head and occurrence maps in the original binary
product derivative, for the very same supplied geometric witness. -/
structure LinkedHeadDerivativeOccurrence
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {Δ Γ U : Segment.{uV,uF} T} {I : Option (Segment.{uV,uF} T)}
    (w : Segment.LinkedTerminalWitness Δ Γ U I)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (τ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier)) where
  head : letI := T.topology
    SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear w.segment.degree F.Carrier)
  head_isHead : T.IsSegmentHead w.segment head
  order_lt : w.cut*Δ.rank + Γ.degree < Δ.degree + Γ.degree
  residual_rank : (Δ.degree+Γ.degree) - (w.cut*Δ.rank+Γ.degree) = w.segment.degree
  space : letI := T.topology
    Subrepresentation ((generalLinearDerivative T ψ (Δ.degree+Γ.degree)
      (w.cut*Δ.rank+Γ.degree) (Nat.le_of_lt order_lt)).obj
      ((T.binaryNormalizedProductFunctor Δ.degree Γ.degree).obj (π,τ))).representation
  quotient : letI := T.topology
    SmoothRep.subrepresentation
      ((generalLinearDerivative T ψ (Δ.degree+Γ.degree)
        (w.cut*Δ.rank+Γ.degree) (Nat.le_of_lt order_lt)).obj
        ((T.binaryNormalizedProductFunctor Δ.degree Γ.degree).obj (π,τ))) space ⟶
      (generalLinearRankCast T residual_rank.symm).obj head
  quotient_surjective : letI := T.topology
    Function.Surjective (SmoothRep.hom quotient)

/-- Construct a genuine residual-head occurrence in the original product,
using the first head's cut quotient and the second head's full top derivative. -/
def linkedHeadDerivativeOccurrence
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {Δ Γ U : Segment.{uV,uF} T} {I : Option (Segment.{uV,uF} T)}
    (w : Segment.LinkedTerminalWitness Δ Γ U I)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (τ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier))
    (hπ : T.IsSegmentHead Δ π) (hτ : T.IsSegmentHead Γ τ) :
    LinkedHeadDerivativeOccurrence T ψ w π τ := by
  letI := T.topology
  apply Classical.choice
  obtain ⟨H,hH,-⟩ := segmentSpecialConstituentExistence F T w.segment
  have hr := witness_cut_rank_le T w
  have hd := witness_residual_rank T w
  have hk : w.cut*Δ.rank+Γ.degree < Δ.degree+Γ.degree := by
    have h := Nat.mul_lt_mul_of_pos_right w.cut_lt Δ.rank_pos
    change w.cut*Δ.rank < Δ.degree at h
    omega
  have hres : (Δ.degree+Γ.degree)-(w.cut*Δ.rank+Γ.degree) = w.segment.degree := by
    omega
  let Q := (generalLinearRankCast T hres.symm).obj H
  let c := headTerminalDerivativeQuotient T ψ Δ w.segment w.cut w.base_eq
    w.length_add_cut hr hd hπ hH
  let R := generalLinearRankCast T hres.symm
  let E : ((generalLinearDerivative T ψ Δ.degree (w.cut*Δ.rank) hr ⋙
      generalLinearRankCast T (by omega : Δ.degree-w.cut*Δ.rank =
        (Δ.degree+Γ.degree)-(w.cut*Δ.rank+Γ.degree))).obj π) ≅
      R.obj ((generalLinearDerivative T ψ Δ.degree (w.cut*Δ.rank) hr ⋙
        generalLinearRankCast T hd).obj π) := by
    apply eqToIso
    change ((generalLinearRankCast T _).obj _) =
      ((generalLinearRankCast T hd ⋙ generalLinearRankCast T hres.symm).obj _)
    rw [generalLinearRankCast_trans]
  let q := E.hom ≫ R.map c.val
  have hq : Function.Surjective (SmoothRep.hom q) :=
    (rankCast_surjective T _ c.val c.property).comp (SmoothRep.hom_hom_surjective E)
  let occ := rightTopDerivativeQuotientOccurrence T ψ hr π τ Q q hq
    (segmentHeadTopDerivativeNontrivial T ψ Γ τ hτ)
  exact ⟨⟨H,hH,hk,hres,occ.1,occ.2.val,occ.2.property⟩⟩

/-- Forgetting the retained maps yields an actual smooth subquotient. -/
theorem LinkedHeadDerivativeOccurrence.isSubquotient
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {Δ Γ U : Segment.{uV,uF} T} {I : Option (Segment.{uV,uF} T)}
    {w : Segment.LinkedTerminalWitness Δ Γ U I}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    {τ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier)}
    (o : LinkedHeadDerivativeOccurrence T ψ w π τ) :
    letI := T.topology
    SmoothRep.IsSubquotient ((generalLinearRankCast T o.residual_rank.symm).obj o.head)
      ((generalLinearDerivative T ψ (Δ.degree+Γ.degree)
        (w.cut*Δ.rank+Γ.degree) (Nat.le_of_lt o.order_lt)).obj
        ((T.binaryNormalizedProductFunctor Δ.degree Γ.degree).obj (π,τ))) := by
  let _ := T.topology
  exact SmoothRep.isSubquotient_iff_exists.mpr
    ⟨_,SmoothRep.subtype _ o.space,o.quotient,
      SmoothRep.subtype_injective _ o.space,o.quotient_surjective⟩

end Langlands.Classification
