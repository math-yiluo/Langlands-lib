import Langlands.Representation.Classification.TwoSupercuspidalPartialDerivatives
import Langlands.Representation.Classification.NondivisibleDerivativeVanishing
import Langlands.Representation.Classification.HighestDerivativeSupportShiftProof
import Langlands.Representation.Classification.RepeatedCuspidalSupportShift
import Langlands.Representation.Induction.SingleBlock

/-! Top derivatives of supplied proper increasing adjacent-product quotients. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.TwoSupercuspidalTopDerivatives

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Rank transport preserves admissibility. -/
theorem isAdmissible_rankCast {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier),
      IsAdmissible A.representation →
        IsAdmissible ((Derivative.generalLinearRankCast T h).obj A).representation := by
  subst h
  exact fun _ hA => hA

/-- A nonzero top derivative of an irreducible admissible source has dimension one. -/
theorem finrank_generalLinearDerivative_top_of_nontrivial
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n : ℕ} (hn : 0 < n) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier),
      A.IsIrreducible → IsAdmissible A.representation →
      Nontrivial ((Derivative.generalLinearDerivative T ψ n n le_rfl).obj A) →
        Module.finrank ℂ ((Derivative.generalLinearDerivative T ψ n n le_rfl).obj A) = 1 := by
  let := T.topology
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  intro A hirr hadm htop
  have key : ∀ (a : ℕ) (ha : a = 0) (h : m + 1 = a + m + 1),
      Nontrivial ((Derivative.generalLinearDerivativePositive T ψ a m).obj
        ((Derivative.generalLinearRankCast T h).obj A)) →
      Module.finrank ℂ ((Derivative.generalLinearDerivativePositive T ψ a m).obj
        ((Derivative.generalLinearRankCast T h).obj A)) = 1 := by
    intro a ha h hnonzero
    subst a
    apply SupercuspidalDerivativesProof.finrank_top_of_multiplicityOne T ψ m _ _ hnonzero
    exact SupercuspidalDerivativesProof.multiplicityOne_of_topologicalData T (0 + m) _ ψ _
      (isAdmissible_rankCast T h A hadm)
      (SupercuspidalTopDerivative.isIrreducible_rankCast T h A hirr)
  exact key (m + 1 - (m + 1)) (Nat.sub_self _)
    (Derivative.rank_eq_of_succ_le le_rfl) htop

/-- An actual irreducible subquotient of a supplied supercuspidal product has
its displayed inducing multiset as a support. -/
theorem support_of_product_subquotient {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    ∀ (A : ∀ i, SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := B.size i))
      (Z : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)),
      Z.IsIrreducible →
      SmoothRep.IsSubquotient Z
        ((T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj)) →
      T.IsSupercuspidalSupport Z
        (List.ofFn (fun i => (⟨B.size i, B.positive i, (A i).isoClass⟩ :
          CuspidalDatum.{max uF uV,uF} T)) : Multiset _) := by
  let := T.topology
  intro A Z hirr hZ
  exact ⟨B.length, _, rfl, B.sum_eq, A, (fun _ => rfl), hirr, hZ⟩

/-- A supercuspidal object has its singleton datum as a support. -/
theorem supercuspidal_singleton_support {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d),
      T.IsSupercuspidalSupport A.obj
        { (⟨d, hd, A.isoClass⟩ : CuspidalDatum.{max uF uV,uF} T) } := by
  let := T.topology
  intro A
  let B : BlockShape d := ⟨1, fun _ => d, fun _ => hd, by simp⟩
  let AA : ∀ i, SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := B.size i) :=
    fun _ => A
  let e₀ := T.singleBlockNormalizedProductEquiv B rfl
    (fun i => (AA i).obj.representation) (fun i => (AA i).obj.isSmooth) 0
  let e : ((T.normalizedProductInductionFunctor B).obj
      (fun i => (AA i).obj)).representation.Equiv A.obj.representation :=
    e₀.trans (Representation.Equiv.mk (LinearEquiv.refl ℂ A.obj) (fun g => by
      have hg : (GeneralLinear.reindex (R := F.Carrier)
          (finCongr (show d = d from B.singleBlock_size rfl 0))).symm g = g := by
        ext i j
        rfl
      change A.obj.representation ((GeneralLinear.reindex (R := F.Carrier)
        (finCongr (B.singleBlock_size rfl 0))).symm g) = A.obj.representation g
      rw [hg]))
  have hZ : SmoothRep.IsSubquotient A.obj
      ((T.normalizedProductInductionFunctor B).obj (fun i => (AA i).obj)) :=
    SmoothRep.IsQuotient.isSubquotient ⟨SmoothRep.ofHom e.toIntertwiningMap,
      e.toLinearEquiv.surjective⟩
  simpa [B, AA, List.ofFn_succ] using
    support_of_product_subquotient T B AA A.obj A.property.1 hZ

/-- A rank-transported equivalence to a supercuspidal object gives its
irreducibility and singleton support before transport. -/
theorem irreducible_support_of_rankCast_equiv {m d : ℕ} (hd : 0 < d) (h : m = d) :
    letI := T.topology
    ∀ (X : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear m F.Carrier))
      (A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      ((Derivative.generalLinearRankCast T h).obj X).representation.Equiv
        A.obj.representation →
      X.IsIrreducible ∧ T.IsSupercuspidalSupport X
        { (⟨d, hd, A.isoClass⟩ : CuspidalDatum.{max uF uV,uF} T) } := by
  subst h
  let := T.topology
  intro X A e
  exact ⟨CuspidalSupport.JacquetLength.isIrreducible_of_equiv e.symm A.property.1,
    (supercuspidal_singleton_support T hd A).of_iso (SmoothRep.mkIso e.symm)⟩

set_option maxHeartbeats 1200000 in
/-- The quotient by a supplied proper subspace of `B × A`, with `A = νB`,
has a nonzero, one-dimensional top derivative. -/
theorem increasing_quotient_top {d : ℕ} (hd : 0 < d)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    ∀ (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
      let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd B.obj A.obj)
      ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
        Nontrivial ((Derivative.generalLinearDerivative T ψ (d + d) (d + d) le_rfl).obj
          (SmoothRep.quotient P S)) ∧
        Module.finrank ℂ
          ((Derivative.generalLinearDerivative T ψ (d + d) (d + d) le_rfl).obj
            (SmoothRep.quotient P S)) = 1 := by
  let := T.topology
  intro B A hAB P S hS₀ hS₁
  let Q := SmoothRep.quotient P S
  have hred : ¬ P.IsIrreducible := by
    intro hirr
    exact (hirr.eq_bot_or_eq_top S).elim hS₀ hS₁
  have hQirr : Q.IsIrreducible :=
    (((TwoSupercuspidalAdjacent.adjacentStructure F T hd
      (CuspidalSupport.nonassociatedJacquetSubquotients F T (d + d))
      (CuspidalSupport.associatedJacquetFiltration F T (d + d)) B A
      (Or.inl hAB)).1 hred).2.2 S hS₀ hS₁).2
  let C := Shahidi.twoBlocks d d hd hd
  let BA : ∀ i, SupercuspidalRep.{uF,max uF uV}
      (F := F.Carrier) (n := C.size i) :=
    Fin.cases B (Fin.cases A finZeroElim)
  have hBA : (fun i => (BA i).obj) = twoBlockFactors hd hd B.obj A.obj := by
    funext i
    fin_cases i <;> rfl
  have hQsub : SmoothRep.IsSubquotient Q
      ((T.normalizedProductInductionFunctor C).obj (fun i => (BA i).obj)) := by
    rw [hBA]
    exact (SmoothRep.quotient_isQuotient S).isSubquotient
  let cB : CuspidalDatum.{max uF uV,uF} T := ⟨d, hd, B.isoClass⟩
  let cA : CuspidalDatum.{max uF uV,uF} T := ⟨d, hd, A.isoClass⟩
  have hcA : cA = cB.twist 1 := congrArg (CuspidalDatum.mk d hd) hAB
  have hsQ : T.IsSupercuspidalSupport Q {cB, cA} := by
    simpa [C, BA, cB, cA, List.ofFn_succ, ← Multiset.cons_coe] using
      support_of_product_subquotient T C BA Q hQirr hQsub
  have hdiv : ∀ i, d ∣ C.size i := by
    intro i
    fin_cases i <;> exact dvd_refl d
  have hvan := supercuspidal_product_subquotient_nondivisible_derivatives T
    (by omega : 0 < d + d) C hdiv BA Q hQsub
  let X := (Derivative.generalLinearDerivative T ψ (d + d) d (Nat.le_add_left d d)).obj Q
  obtain ⟨eX⟩ := (twoSupercuspidalAdjacentProductMiddleDerivatives F T
    ψ d hd B A (Or.inl hAB) S hS₀ hS₁).2
  obtain ⟨hXirr, hsX⟩ := irreducible_support_of_rankCast_equiv T hd
    (Nat.add_sub_cancel d d) X A eX
  have hXnt : Nontrivial X :=
    SupercuspidalTopDerivative.nontrivial_of_isIrreducible X.representation hXirr
  have htop : Nontrivial
      ((Derivative.generalLinearDerivative T ψ (d + d) (d + d) le_rfl).obj Q) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hzero
    have hhigh : ∀ (j : ℕ) (hj : j ≤ d + d), d < j →
        Subsingleton ((Derivative.generalLinearDerivative T ψ (d + d) j hj).obj Q) := by
      intro j hj hdj
      by_cases heq : j = d + d
      · subst j
        exact hzero
      · apply hvan ψ j hj (by omega) (by omega)
        intro hdvd
        have heq := Nat.eq_of_dvd_of_lt_two_mul (by omega : j ≠ 0) hdvd
          (by omega : j < 2 * d)
        omega
    have hshift := highestDerivativeSupportShift.{uF,max uF uV} F T
      ψ (d + d) Q d (Nat.le_add_left d d) hQirr hXnt hhigh X
      ⟨hXirr, Representation.IntertwiningMap.id X.representation, Function.injective_id⟩
      {cB, cA} {cA} hsQ hsX
    have hu := RepeatedCuspidalSupport.upper_not_mem_of_shift_le T cB 1 1 {cA}
      (by simpa [RepeatedCuspidalSupport.pairSupport, ← hcA, or_comm] using hshift)
    exact hu (by simp [← hcA])
  exact ⟨htop, finrank_generalLinearDerivative_top_of_nontrivial T ψ (by omega)
    Q hQirr (CuspidalSupport.cuspidalEmbedding F T (d + d) Q hQirr).1 htop⟩

end Langlands.Classification.TwoSupercuspidalTopDerivatives

namespace Langlands.Classification

open GeneralLinear

universe uF uV

/-- Top derivatives of the quotient by any supplied nonzero proper invariant
subspace of an increasing adjacent supercuspidal pair. -/
def TwoSupercuspidalIncreasingProductQuotientTopDerivative
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (d : ℕ) (hd : 0 < d)
    (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
    A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
    let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
      (twoBlockFactors hd hd B.obj A.obj)
    ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
      Nontrivial ((Derivative.generalLinearDerivative T ψ (d + d) (d + d) le_rfl).obj
        (SmoothRep.quotient P S)) ∧
      Module.finrank ℂ
        ((Derivative.generalLinearDerivative T ψ (d + d) (d + d) le_rfl).obj
          (SmoothRep.quotient P S)) = 1

set_option maxHeartbeats 1200000 in
/-- Highest-derivative support shift and Whittaker multiplicity one prove the
top-derivative assertion for supplied increasing-product quotients. -/
theorem twoSupercuspidalIncreasingProductQuotientTopDerivative
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TwoSupercuspidalIncreasingProductQuotientTopDerivative.{uF,uV} F T :=
  fun ψ d hd =>
    TwoSupercuspidalTopDerivatives.increasing_quotient_top.{uF,uV} T (d := d) hd ψ

end Langlands.Classification
