import Langlands.Representation.Classification.AdjacentQuotientUpperProductDerivatives
import Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.Representation.Filtration.SubquotientAlgebraProof
import Langlands.Representation.Filtration.FunctorLengthTwoDetection
import Mathlib.Order.Atoms

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.AdjacentQuotientUpperProductFirstDerivative

open GeneralLinear Derivative PadicField.TopologicalData AdjacentQuotientUpperProductDerivatives

universe uF uV uK uG uW uC vC uι

/-- A nonzero finite-length smooth representation has an actual irreducible
invariant subspace. -/
theorem exists_irreducible_subrepresentation {K : Type uK} [Field K]
    {G : Type uG} [Group G] [TopologicalSpace G]
    (X : SmoothRep.{uK,uG,uW} K G) (hX : X.HasFiniteLength) [Nontrivial X] :
    ∃ D : SmoothRep.{uK,uG,uW} K G, D.IsIrreducible ∧
      ∃ j : D.representation.IntertwiningMap X.representation, Function.Injective j := by
  let : IsArtinian (MonoidAlgebra K G) X.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hX).2
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := X.representation)
  let : IsAtomic (Subrepresentation X.representation) := e.isAtomic_iff.mpr inferInstance
  have hbt : (⊥ : Subrepresentation X.representation) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    have hx0 : x ∈ (⊥ : Subrepresentation X.representation) := by
      rw [h]
      trivial
    exact hx hx0
  let : Nontrivial (Subrepresentation X.representation) := ⟨⊥, ⊤, hbt⟩
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Subrepresentation X.representation)
  have hirr := (LengthCriterionProof.isIrreducible_quotientRep_iff
    (bot_le : (⊥ : Subrepresentation X.representation) ≤ S)).mpr hS.bot_covBy
  obtain ⟨eS⟩ := FunctorLengthTwo.nonempty_quotientBot_equiv S
  refine ⟨X.subrepresentation S, ?_, FunctorLengthTwo.subtypeMap S,
    Subtype.val_injective⟩
  exact CuspidalSupport.JacquetLength.isIrreducible_of_equiv eS hirr

/-- Actual gluing whose pieces are zero or copies of two specified objects
preserves finite length and detects each irreducible constituent in one of them. -/
theorem finiteLength_support_of_glued_two {K : Type uK} [Field K]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {C : Type uC} [Category.{vC} C]
    (M : C ⥤ SmoothRep.{uK,uG,uW} K G)
    {ι : Type uι} [Fintype ι] {P : ι → C ⥤ Rep.{uW} K G}
    (h : IsGluedFromFamily (M ⋙ SmoothRep.toRep) P)
    (X : C) (U V : SmoothRep.{uK,uG,uW} K G)
    (hU : U.HasFiniteLength) (hV : V.HasFiniteLength)
    (hP : ∀ i, Subsingleton ((P i).obj X) ∨
      Nonempty (((P i).obj X).ρ.Equiv U.representation) ∨
      Nonempty (((P i).obj X).ρ.Equiv V.representation)) :
    (M.obj X).HasFiniteLength ∧
      ∀ D : SmoothRep.{uK,uG,uW} K G, D.IsIrreducible →
        SmoothRep.IsSubquotient D (M.obj X) →
        SmoothRep.IsSubquotient D U ∨ SmoothRep.IsSubquotient D V := by
  constructor
  · apply finiteLength_of_glued h X
    intro i
    apply Module.length_ne_top_iff.mp
    change repLength ((P i).obj X).ρ ≠ ⊤
    rcases hP i with hz | heU | heV
    · rw [repLength_eq_zero_iff.mpr hz]
      simp
    · obtain ⟨eU⟩ := heU
      rw [repLength_congr eU]
      exact Module.length_ne_top_iff.mpr hU
    · obtain ⟨eV⟩ := heV
      rw [repLength_congr eV]
      exact Module.length_ne_top_iff.mpr hV
  · intro D hD hDX
    obtain ⟨e, σ, s, hs⟩ := h
    let t : ObjectRepFiltration (M.obj X).obj _ := evaluatedFiltration s X
    obtain ⟨j, hj⟩ := t.exists_smoothGradedObject_subquotient hD hDX
    obtain ⟨ej⟩ := hs j
    let eG := (evaluatedGradedEquiv s X j).trans (Representation.equivOfIso (ej.app X))
    rcases hP (e (σ j)) with hz | heU | heV
    · have hz' : Subsingleton (t.smoothGradedObject j) :=
        ⟨fun v w => eG.injective (hz.elim _ _)⟩
      have hDz := subsingleton_of_isSubquotient hj hz'
      have : D.representation.IsIrreducible := hD
      let : Nontrivial D :=
        IsSimpleModule.nontrivial (MonoidAlgebra K G) D.representation.asModule
      exact False.elim (not_subsingleton D hDz)
    · obtain ⟨eU⟩ := heU
      exact Or.inl (hj.of_iso_right (SmoothRep.mkIso (eG.trans eU)))
    · obtain ⟨eV⟩ := heV
      exact Or.inr (hj.of_iso_right (SmoothRep.mkIso (eG.trans eV)))

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Products of two positive-rank irreducible factors have finite length. -/
theorem binary_finite_length {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (X : SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
      (Y : SmoothRep.{0,uF,uV} ℂ (GeneralLinear b F.Carrier)),
      X.IsIrreducible → Y.IsIrreducible →
      ((T.binaryNormalizedProductFunctor a b).obj (X,Y)).HasFiniteLength := by
  let := T.topology
  intro X Y hX hY
  rw [BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks F T ha hb]
  apply irreducibleProductFiniteLength F T (a+b) (by omega)
  intro i
  fin_cases i <;> assumption

/-- The supplied proper quotient of the increasing adjacent product is
irreducible; existence of such a subspace remains a premise. -/
theorem quotient_irreducible {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
      let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd B.obj A.obj)
      ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
        (SmoothRep.quotient P S).IsIrreducible := by
  let := T.topology
  intro B A hAB P S hS₀ hS₁
  have hred : ¬ P.IsIrreducible := fun hirr =>
    (hirr.eq_bot_or_eq_top S).elim hS₀ hS₁
  exact (((TwoSupercuspidalAdjacent.adjacentStructure F T hd
    (CuspidalSupport.nonassociatedJacquetSubquotients F T (d+d))
    (CuspidalSupport.associatedJacquetFiltration F T (d+d)) B A (Or.inl hAB)).1
      hred).2.2 S hS₀ hS₁).2

/-- Rank transports of the factors and target commute with their actual
binary-product equivalences. -/
def product_rankCast_equiv {a b a' b' c : ℕ}
    (ha : a = a') (hb : b = b') (h : a+b = c) (h' : a'+b' = c) :
    letI := T.topology
    ∀ (X : SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
      (Y : SmoothRep.{0,uF,uV} ℂ (GeneralLinear b F.Carrier))
      (X' : SmoothRep.{0,uF,uV} ℂ (GeneralLinear a' F.Carrier))
      (Y' : SmoothRep.{0,uF,uV} ℂ (GeneralLinear b' F.Carrier)),
      ((generalLinearRankCast T ha).obj X).representation.Equiv X'.representation →
      ((generalLinearRankCast T hb).obj Y).representation.Equiv Y'.representation →
      ((generalLinearRankCast T h).obj
        ((T.binaryNormalizedProductFunctor a b).obj (X,Y))).representation.Equiv
      ((generalLinearRankCast T h').obj
        ((T.binaryNormalizedProductFunctor a' b').obj (X',Y'))).representation := by
  subst a' b' c
  let := T.topology
  intro X Y X' Y' eX eY
  exact SmoothRep.equivOfIso ((T.binaryNormalizedProductFunctor a b).mapIso
    (Iso.prod (SmoothRep.mkIso eX) (SmoothRep.mkIso eY)))

/-- Rank transport preserves actual finite length. -/
theorem finite_length_rankCast {a b : ℕ} (h : a=b) :
    letI := T.topology
    ∀ X : SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier),
      X.HasFiniteLength → ((generalLinearRankCast T h).obj X).HasFiniteLength := by
  subst h
  exact fun _ hX => hX

/-- Every actual order-d grade is zero, a transported copy of Q, or a
transported copy of the product A × A. -/
theorem order_d_piece {d : ℕ} (hd : 0 < d)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    ∀ (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
      let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd B.obj A.obj)
      ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
      ∀ x : LeibnizIndex (d+d) d d,
        let G := (leibnizPiece T ψ (d+d) d d x).obj (SmoothRep.quotient P S, A.obj)
        let h : d+d = ((d+d)+d)-d := by omega
        Subsingleton G ∨
          Nonempty (G.ρ.Equiv
            ((generalLinearRankCast T h).obj (SmoothRep.quotient P S)).representation) ∨
          Nonempty (G.ρ.Equiv
            ((generalLinearRankCast T h).obj
              ((T.binaryNormalizedProductFunctor d d).obj (A.obj,A.obj))).representation) := by
  let := T.topology
  intro B A hAB P S hS₀ hS₁ x
  rcases x with ⟨⟨i,j⟩,hx⟩
  have hx' := mem_leibnizIndices.mp hx
  by_cases hj₀ : j = 0
  · subst j
    have hi : i = d := by omega
    subst i
    right
    right
    obtain ⟨eQ⟩ := (twoSupercuspidalAdjacentProductMiddleDerivatives.{uF,max uF uV}
      F T ψ d hd B A (Or.inl hAB) S hS₀ hS₁).2
    exact ⟨product_rankCast_equiv T (Nat.add_sub_cancel d d) rfl
      (leibnizIndices_rank hx) (by omega)
      ((generalLinearDerivative T ψ (d+d) d (by omega)).obj (SmoothRep.quotient P S))
      A.obj A.obj A.obj eQ (Representation.Equiv.refl _)⟩
  by_cases hjd : j = d
  · subst j
    have hi : i = 0 := by omega
    subst i
    right
    left
    have hA := TwoSupercuspidalPartialDerivatives.finrank_topDerivative.{uF,max uF uV}
      T ψ hd A
    change Module.finrank ℂ
      ((generalLinearRankCast T (Nat.sub_self d)).obj
        ((generalLinearDerivative T ψ d d le_rfl).obj A.obj)) = 1 at hA
    rw [TwoSupercuspidalPartialDerivatives.finrank_rankCast] at hA
    obtain ⟨eP⟩ := BinaryProductBridge.nonempty_equiv_rankCast_product_right.{uF,max uF uV}
      F T (Nat.sub_self d) (leibnizIndices_rank hx) (by omega)
      (SmoothRep.quotient P S) ((generalLinearDerivative T ψ d d le_rfl).obj A.obj) hA
    exact ⟨eP.symm⟩
  · left
    have hA := SupercuspidalDerivativeVanishing.subsingleton_generalLinearDerivative
      T ψ d j hx'.2.1 (by omega) (by omega) A.obj A.property.2
    exact BinaryProductBridge.subsingleton_rankCast_product.{uF,max uF uV}
      F T (leibnizIndices_rank hx) _ _ (Or.inr hA)

/-- The order-d derivative has finite length and each irreducible actual
subquotient occurs in Q or in A × A, after the indicated rank transport. -/
theorem order_d_finiteLength_support {d : ℕ} (hd : 0 < d)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    ∀ (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
      let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd B.obj A.obj)
      ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
        let R := (generalLinearDerivative T ψ ((d+d)+d) d (by omega)).obj
          ((T.binaryNormalizedProductFunctor (d+d) d).obj
            (SmoothRep.quotient P S,A.obj))
        let h : d+d = ((d+d)+d)-d := by omega
        R.HasFiniteLength ∧
          ∀ D : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (((d+d)+d)-d) F.Carrier),
            D.IsIrreducible → SmoothRep.IsSubquotient D R →
            SmoothRep.IsSubquotient D ((generalLinearRankCast T h).obj (SmoothRep.quotient P S)) ∨
            SmoothRep.IsSubquotient D ((generalLinearRankCast T h).obj
              ((T.binaryNormalizedProductFunctor d d).obj (A.obj,A.obj))) := by
  let := T.topology
  intro B A hAB P S hS₀ hS₁
  let M := T.binaryNormalizedProductFunctor.{uF,max uF uV} (d+d) d ⋙
    generalLinearDerivative T ψ ((d+d)+d) d (by omega)
  have hglue := AdjacentQuotientUpperProduct.positiveGlued.{uF,max uF uV}
    T (by omega : 0 < d+d) hd ψ d ⟨hd,by omega⟩
  exact finiteLength_support_of_glued_two M hglue (SmoothRep.quotient P S,A.obj) _ _
    (finite_length_rankCast T _ _ (SmoothRep.hasFiniteLength_of_isIrreducible
      (quotient_irreducible.{uF,uV} T hd B A hAB S hS₀ hS₁)))
    (finite_length_rankCast T _ _ (binary_finite_length T hd hd A.obj A.obj
      A.property.1 A.property.1))
    (order_d_piece.{uF,uV} T hd ψ B A hAB S hS₀ hS₁)

/-- Every irreducible actual subquotient of a two-factor supercuspidal product
has the displayed two-entry support. -/
theorem pair_support {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ (X Y : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d))
      (D : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (d+d) F.Carrier)),
      D.IsIrreducible → SmoothRep.IsSubquotient D
        ((T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
          (twoBlockFactors hd hd X.obj Y.obj)) →
      T.IsSupercuspidalSupport D
        {(⟨d,hd,X.isoClass⟩ : CuspidalDatum.{max uF uV,uF} T),
         (⟨d,hd,Y.isoClass⟩ : CuspidalDatum.{max uF uV,uF} T)} := by
  let := T.topology
  intro X Y D hD hDX
  let C := Shahidi.twoBlocks d d hd hd
  let XY : ∀ i, SupercuspidalRep.{uF,max uF uV}
      (F := F.Carrier) (n := C.size i) := Fin.cases X (Fin.cases Y finZeroElim)
  have hXY : (fun i => (XY i).obj) = twoBlockFactors hd hd X.obj Y.obj := by
    funext i
    fin_cases i <;> rfl
  have hDP : SmoothRep.IsSubquotient D
      ((T.normalizedProductInductionFunctor C).obj (fun i => (XY i).obj)) := by
    rw [hXY]
    exact hDX
  simpa [C,XY,List.ofFn_succ,← Multiset.cons_coe] using
    TwoSupercuspidalTopDerivatives.support_of_product_subquotient T C XY D hD hDP

/-- A universal support assertion for actual irreducible subquotients survives
rank transport of its source. -/
theorem support_of_subquotient_rankCast {a b : ℕ} (h : a=b) :
    letI := T.topology
    ∀ (X : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
      (s : Multiset (CuspidalDatum.{max uF uV,uF} T)),
      (∀ D : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier),
        D.IsIrreducible → SmoothRep.IsSubquotient D X → T.IsSupercuspidalSupport D s) →
      ∀ D : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear b F.Carrier),
        D.IsIrreducible → SmoothRep.IsSubquotient D ((generalLinearRankCast T h).obj X) →
        T.IsSupercuspidalSupport D s := by
  subst h
  exact fun _ _ hs => hs

/-- Every irreducible actual subquotient of the order-d derivative has a
supercuspidal support containing the upper datum. -/
theorem order_d_upper_support {d : ℕ} (hd : 0 < d)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    ∀ (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
      let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd B.obj A.obj)
      ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
        let R := (generalLinearDerivative T ψ ((d+d)+d) d (by omega)).obj
          ((T.binaryNormalizedProductFunctor (d+d) d).obj
            (SmoothRep.quotient P S,A.obj))
        ∀ D : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (((d+d)+d)-d) F.Carrier),
          D.IsIrreducible → SmoothRep.IsSubquotient D R →
          ∃ s : Multiset (CuspidalDatum.{max uF uV,uF} T),
            T.IsSupercuspidalSupport D s ∧ (⟨d,hd,A.isoClass⟩ : CuspidalDatum T) ∈ s := by
  let := T.topology
  intro B A hAB P S hS₀ hS₁ R D hD hDR
  let cB : CuspidalDatum.{max uF uV,uF} T := ⟨d,hd,B.isoClass⟩
  let cA : CuspidalDatum.{max uF uV,uF} T := ⟨d,hd,A.isoClass⟩
  rcases (order_d_finiteLength_support.{uF,uV} T hd ψ B A hAB S hS₀ hS₁).2 D hD hDR with hDQ | hDAA
  · refine ⟨{cB,cA},?_,by simp [cA]⟩
    apply support_of_subquotient_rankCast T _ (SmoothRep.quotient P S) {cB,cA} _ D hD hDQ
    intro E hE hEQ
    exact pair_support T hd B A E hE
      (smoothSubquotientTransitivity ℂ _ P (SmoothRep.quotient P S) E hEQ
        (SmoothRep.quotient_isQuotient S).isSubquotient)
  · refine ⟨{cA,cA},?_,by simp [cA]⟩
    apply support_of_subquotient_rankCast T _
      ((T.binaryNormalizedProductFunctor d d).obj (A.obj,A.obj)) {cA,cA} _ D hD hDAA
    intro E hE hEAA
    rw [BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks F T hd hd] at hEAA
    exact pair_support T hd A A E hE hEAA

end Langlands.Classification.AdjacentQuotientUpperProductFirstDerivative

namespace Langlands.Classification

open GeneralLinear Derivative PadicField.TopologicalData

universe uF uV

/-- The order-d derivative of a supplied increasing adjacent quotient times
its upper factor has finite length, and all its irreducible constituents have
an actual supercuspidal support containing that upper factor. -/
def IncreasingAdjacentQuotientUpperProductFirstDerivative
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (d : ℕ) (hd : 0 < d)
    (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
    A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
    let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
      (twoBlockFactors hd hd B.obj A.obj)
    ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
      let R := (generalLinearDerivative T ψ ((d+d)+d) d (by omega)).obj
        ((T.binaryNormalizedProductFunctor (d+d) d).obj
          (SmoothRep.quotient P S,A.obj))
      R.HasFiniteLength ∧
        ∀ D : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (((d+d)+d)-d) F.Carrier),
          D.IsIrreducible → SmoothRep.IsSubquotient D R →
          ∃ s : Multiset (CuspidalDatum.{max uF uV,uF} T),
            T.IsSupercuspidalSupport D s ∧ (⟨d,hd,A.isoClass⟩ : CuspidalDatum T) ∈ s

/-- Actual Leibniz pieces Q and A × A establish the first common-rank
proper derivative assertion. -/
theorem increasingAdjacentQuotientUpperProductFirstDerivative
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    IncreasingAdjacentQuotientUpperProductFirstDerivative.{uF,uV} F T := by
  let := T.topology
  intro ψ d hd B A hAB P S hS₀ hS₁
  exact ⟨(AdjacentQuotientUpperProductFirstDerivative.order_d_finiteLength_support.{uF,uV}
      T hd ψ B A hAB S hS₀ hS₁).1,
    AdjacentQuotientUpperProductFirstDerivative.order_d_upper_support.{uF,uV}
      T hd ψ B A hAB S hS₀ hS₁⟩

end Langlands.Classification
