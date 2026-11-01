import Langlands.Representation.CuspidalSupport.TripleInductionMaps
import Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement
import Langlands.Representation.Induction.RankCast

/-! The actual two-factor swap with literal reversed block ranks. -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.CuspidalSupport

open GeneralLinear Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem productObj_congr {r : ℕ} {C C' : BlockShape r} (h : C = C')
    (A : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (C.size i) F.Carrier))
    (A' : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (C'.size i) F.Carrier))
    (hA : HEq A A') :
    letI := T.topology
    (T.normalizedProductInductionFunctor C).obj A =
      (T.normalizedProductInductionFunctor C').obj A' := by
  subst h
  cases hA
  rfl

/-- Swapping the two block labels and transporting the total rank gives
the literal reversed two-block shape. -/
theorem twoBlocks_swap_rankCast {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ((Shahidi.twoBlocks a b ha hb).permute
      ((Shahidi.twoBlocks a b ha hb).adjacentSwap 0 (by change 1 < 2; decide))).rankCast
        (Nat.add_comm a b) = Shahidi.twoBlocks b a hb ha := by
  apply BlockShape.ext_of_size
    (B₁ := ((Shahidi.twoBlocks a b ha hb).permute
      ((Shahidi.twoBlocks a b ha hb).adjacentSwap 0 (by change 1 < 2; decide))).rankCast
        (Nat.add_comm a b))
    (B₂ := Shahidi.twoBlocks b a hb ha) rfl
  intro i
  fin_cases i <;>
    simp [BlockShape.permute, BlockShape.rankCast, BlockShape.adjacentSwap,
      Shahidi.twoBlocks]

/-- An actual equivalence from an irreducible two-block product to the
literal reversed product, pulled back by the entry-preserving total-rank
reindex. The factors may have different positive ranks. -/
def irreducibleLiteralTwoBlockSwapEquiv {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear b F.Carrier)),
      A.IsIrreducible → B.IsIrreducible →
      ((T.normalizedProductInductionFunctor (Shahidi.twoBlocks a b ha hb)).obj
        (twoBlockFactors ha hb A B)).IsIrreducible →
      Representation.Equiv
        (((T.normalizedProductInductionFunctor (Shahidi.twoBlocks a b ha hb)).obj
          (twoBlockFactors ha hb A B)).representation)
        ((((T.normalizedProductInductionFunctor (Shahidi.twoBlocks b a hb ha)).obj
          (twoBlockFactors hb ha B A)).representation).comp
            (reindex (R := F.Carrier) (finCongr (Nat.add_comm a b))).toMonoidHom) := by
  letI := T.topology
  intro A B hA hB hP
  let C := Shahidi.twoBlocks a b ha hb
  let s := C.adjacentSwap 0 (by change 1 < 2; decide)
  let X := twoBlockFactors ha hb A B
  have hX : ∀ i, (X i).IsIrreducible := by
    intro i
    fin_cases i
    · exact hA
    · exact hB
  let e := SmoothRep.equivOfIso (irreducibleTwoFactorSwapIso F T C rfl X hX hP)
  let Y := fun i => X (s i)
  have hY : HEq Y (twoBlockFactors hb ha B A) := by
    apply Function.hfunext rfl
    intro i j hij
    cases hij
    fin_cases i <;> rfl
  have hobj := productObj_congr F T (twoBlocks_swap_rankCast ha hb)
    Y (twoBlockFactors hb ha B A) hY
  let erank := T.normalizedProductInducedRankCastEquiv (C.permute s)
    (Nat.add_comm a b) (fun i => (Y i).representation)
  exact (e.trans erank.symm).trans
    ((SmoothRep.equivOfIso (eqToIso hobj)).precomp
      (reindex (R := F.Carrier) (finCongr (Nat.add_comm a b))).toMonoidHom)

/-- An irreducible literal two-block product of irreducible factors admits
an actual equivalence to the literal reversed product at the same ambient
rank after entry-preserving reindexing. -/
def IrreducibleLiteralTwoBlockSwap : Prop :=
  letI := T.topology
  ∀ (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
    (B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear b F.Carrier)),
    A.IsIrreducible → B.IsIrreducible →
    ((T.normalizedProductInductionFunctor (Shahidi.twoBlocks a b ha hb)).obj
      (twoBlockFactors ha hb A B)).IsIrreducible →
    Nonempty (Representation.Equiv
      (((T.normalizedProductInductionFunctor (Shahidi.twoBlocks a b ha hb)).obj
        (twoBlockFactors ha hb A B)).representation)
      ((((T.normalizedProductInductionFunctor (Shahidi.twoBlocks b a hb ha)).obj
        (twoBlockFactors hb ha B A)).representation).comp
          (reindex (R := F.Carrier) (finCongr (Nat.add_comm a b))).toMonoidHom))

/-- Literal two-block swap, retaining the actual equivalence. -/
theorem irreducibleLiteralTwoBlockSwap :
    IrreducibleLiteralTwoBlockSwap.{uF,uV} F T := by
  intro a b ha hb A B hA hB hP
  exact ⟨irreducibleLiteralTwoBlockSwapEquiv F T ha hb A B hA hB hP⟩

end Langlands.CuspidalSupport
