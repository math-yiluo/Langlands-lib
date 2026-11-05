import Langlands.Representation.Derivative.LeibnizConstituentExtraction
import Langlands.Representation.Tensor.OneFactorQuotient

/-! # Actual quotient occurrences in binary-product derivatives -/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Each specified feasible Leibniz grade is the quotient of an actual invariant
subspace of the whole product derivative. -/
def leibnizSmoothPieceQuotient
    {a b d : ℕ} (hd : d ≤ a + b) (x : LeibnizIndex a b d)
    (A : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    let J := (generalLinearDerivative T ψ (a+b) d hd).obj
      ((T.binaryNormalizedProductFunctor a b).obj (A,B))
    Σ S : Subrepresentation J.representation,
      {q : SmoothRep.subrepresentation J S ⟶
        (leibnizSmoothPiece T ψ a b d x).obj (A,B) //
        Function.Surjective (SmoothRep.hom q)} := by
  letI := T.topology
  exact Classical.choice (by
    obtain ⟨e,s,hs⟩ :=
      (generalLinearDerivativeLeibnizFiltration.{uF,uV} F T).filtration T ψ a b d hd
    let j := e x
    obtain ⟨E⟩ := hs j
    let E' := E.app (A,B) ≪≫ eqToIso
      (congrArg (fun y => (leibnizPiece T ψ a b d y).obj (A,B)) (e.symm_apply_apply x))
    let J := (generalLinearDerivative T ψ (a+b) d hd).obj
      ((T.binaryNormalizedProductFunctor a b).obj (A,B))
    let S := (s.step j.succ).obj (A,B)
    let q₀ := ((s.step j.castSucc).quotientNatProjection (s.step j.succ)).app (A,B)
    let q : SmoothRep.subrepresentation J S ⟶
        (leibnizSmoothPiece T ψ a b d x).obj (A,B) :=
      SmoothRep.ofHom ((Representation.equivOfIso E').toIntertwiningMap.comp q₀.hom)
    exact ⟨⟨S,q,(Representation.equivOfIso E').surjective.comp
      ((s.step j.castSucc).quotientProjection_surjective (s.step j.succ) (A,B))⟩⟩)

private theorem rankCast_surjective {m n : ℕ} (h : m = n)
    {A B : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (q : letI := T.topology; A ⟶ B)
    (hq : letI := T.topology; Function.Surjective (SmoothRep.hom q)) :
    letI := T.topology
    Function.Surjective (SmoothRep.hom ((generalLinearRankCast T h).map q)) := by
  subst n
  exact hq

private def rightZeroProductQuotient {a b : ℕ} (hb : b = 0)
    (A : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hB : Nontrivial B) :
    letI := T.topology
    {q : (T.binaryNormalizedProductFunctor a b).obj (A,B) ⟶
      (generalLinearRankCast T (by omega : a = a+b)).obj A //
      Function.Surjective (SmoothRep.hom q)} := by
  letI := T.topology
  subst b
  letI := hB
  let E := T.binaryRightZeroTensorEquiv rfl (A,B)
  let c := BinaryTensor.firstFactorQuotient A.representation B
  let c' : (BinaryTensor.rankZeroRight (R := F.Carrier) rfl A.representation B).IntertwiningMap
      A.representation :=
    { toLinearMap := c.val.toLinearMap
      isIntertwining' g := by
        simpa only [BinaryTensor.rankZeroRight, MonoidHom.comp_apply,
          GeneralLinear.reindex_finCongr_rfl, MulEquiv.coe_toMonoidHom,
          MulEquiv.refl_apply] using c.val.isIntertwining' g }
  exact ⟨SmoothRep.ofHom (c'.comp E.toIntertwiningMap),c.property.comp E.surjective⟩

/-- A supplied quotient of the first factor's order-r derivative occurs in the
order-(r+b) derivative of the binary product when the second full top derivative
is nonzero. The result retains an actual invariant subspace and surjection. -/
def rightTopDerivativeQuotientOccurrence
    {a b r : ℕ} (hr : r ≤ a)
    (A : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear b F.Carrier))
    (Q : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((a+b)-(r+b)) F.Carrier))
    (q : letI := T.topology
      ((generalLinearDerivative T ψ a r hr ⋙
        generalLinearRankCast T (by omega : a-r = (a+b)-(r+b))).obj A) ⟶ Q)
    (hq : letI := T.topology; Function.Surjective (SmoothRep.hom q))
    (hB : Nontrivial ((generalLinearDerivative T ψ b b le_rfl).obj B)) :
    letI := T.topology
    let J := (generalLinearDerivative T ψ (a+b) (r+b) (by omega)).obj
      ((T.binaryNormalizedProductFunctor a b).obj (A,B))
    Σ S : Subrepresentation J.representation,
      {f : SmoothRep.subrepresentation J S ⟶ Q //
        Function.Surjective (SmoothRep.hom f)} := by
  letI := T.topology
  let x : LeibnizIndex a b (r+b) :=
    ⟨(r,b),mem_leibnizIndices.mpr ⟨hr,le_rfl,rfl⟩⟩
  let DA := (generalLinearDerivative T ψ a r hr).obj A
  let DB := (generalLinearDerivative T ψ b b le_rfl).obj B
  let c := rightZeroProductQuotient T (Nat.sub_self b) DA DB hB
  let R := generalLinearRankCast T (leibnizIndices_rank x.property)
  let E : R.obj ((generalLinearRankCast T (by omega : a-r = (a-r)+(b-b))).obj DA) ≅
      (generalLinearRankCast T (by omega : a-r = (a+b)-(r+b))).obj DA := by
    apply eqToIso
    change ((generalLinearRankCast T _ ⋙ generalLinearRankCast T _).obj DA) = _
    rw [generalLinearRankCast_trans]
  let c' := R.map c.val ≫ E.hom ≫ q
  have hc' : Function.Surjective (SmoothRep.hom c') :=
    hq.comp ((SmoothRep.hom_hom_surjective E).comp
      (rankCast_surjective T _ c.val c.property))
  let w := leibnizSmoothPieceQuotient T ψ (by omega : r+b ≤ a+b) x A B
  exact ⟨w.1,w.2.val ≫ c',hc'.comp w.2.property⟩

/-- The actual maps above give an actual smooth subquotient occurrence. -/
theorem rightTopDerivativeQuotient_isSubquotient
    {a b r : ℕ} (hr : r ≤ a)
    (A : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear b F.Carrier))
    (Q : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((a+b)-(r+b)) F.Carrier))
    (q : letI := T.topology
      ((generalLinearDerivative T ψ a r hr ⋙
        generalLinearRankCast T (by omega : a-r = (a+b)-(r+b))).obj A) ⟶ Q)
    (hq : letI := T.topology; Function.Surjective (SmoothRep.hom q))
    (hB : Nontrivial ((generalLinearDerivative T ψ b b le_rfl).obj B)) :
    letI := T.topology
    SmoothRep.IsSubquotient Q
      ((generalLinearDerivative T ψ (a+b) (r+b) (by omega)).obj
        ((T.binaryNormalizedProductFunctor a b).obj (A,B))) := by
  let _ := T.topology
  let w := rightTopDerivativeQuotientOccurrence T ψ hr A B Q q hq hB
  exact SmoothRep.isSubquotient_iff_exists.mpr
    ⟨_,SmoothRep.subtype _ w.1,w.2.val,SmoothRep.subtype_injective _ w.1,w.2.property⟩

end Langlands.Derivative
