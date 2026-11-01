import Langlands.Representation.Classification.AdjacentQuotientUpperProduct
import Langlands.Representation.Filtration.ActualGradedExtraction
import Langlands.Representation.Filtration.RepresentationLength
import Langlands.Representation.Smooth.IrreducibleRealization
import Langlands.Representation.Smooth.ConstituentSupport
import Mathlib.Data.ENat.BigOperators

/-! Proper derivatives of a supplied increasing quotient times its upper factor. -/

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.AdjacentQuotientUpperProductDerivatives

open GeneralLinear Derivative

universe uF uV uK uG uW uC vC uι

/-- Evaluate every actual filtration step at one object. -/
def evaluatedFiltration {K : Type uK} [Field K] {G : Type uG} [Monoid G]
    {C : Type uC} [Category.{vC} C] {M : C ⥤ Rep.{uW} K G}
    {n : ℕ} (s : RepFunctorFiltration M n) (X : C) :
    ObjectRepFiltration (M.obj X) n :=
  ObjectRepFiltration.ofSubrepresentations (fun i => (s.step i).obj X)
    (s.monotone X) (s.zero X) (s.top X)

/-- The evaluated actual quotient retains its quotient action and carrier. -/
def evaluatedGradedEquiv {K : Type uK} [Field K] {G : Type uG} [Monoid G]
    {C : Type uC} [Category.{vC} C] {M : C ⥤ Rep.{uW} K G}
    {n : ℕ} (s : RepFunctorFiltration M n) (X : C) (j : Fin n) :
    ((evaluatedFiltration s X).gradedRepresentation j).ρ.Equiv
      ((s.graded j).obj X).ρ :=
  Representation.Equiv.refl _

/-- Finite group-algebra length of every graded value implies finite length
of the actual glued value. -/
theorem finiteLength_of_glued {K : Type uK} [Field K] {G : Type uG} [Group G]
    {C : Type uC} [Category.{vC} C] {M : C ⥤ Rep.{uW} K G}
    {ι : Type uι} [Fintype ι] {P : ι → C ⥤ Rep.{uW} K G}
    (h : IsGluedFromFamily M P) (X : C)
    (hP : ∀ i, IsFiniteLength (MonoidAlgebra K G) ((P i).obj X).ρ.asModule) :
    IsFiniteLength (MonoidAlgebra K G) (M.obj X).ρ.asModule := by
  obtain ⟨e, σ, s, hs⟩ := h
  apply Module.length_ne_top_iff.mp
  change repLength (M.obj X).ρ ≠ ⊤
  rw [repLength_eq_sum_of_filtration (evaluatedFiltration s X)]
  apply ENat.sum_ne_top.mpr
  intro j _
  obtain ⟨ej⟩ := hs j
  rw [repLength_congr ((evaluatedGradedEquiv s X j).trans
    (Representation.equivOfIso (ej.app X)))]
  exact Module.length_ne_top_iff.mpr (hP _)

/-- An actual subquotient of a zero smooth object is zero. -/
theorem subsingleton_of_isSubquotient {K : Type uK} [Field K]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {A D : SmoothRep.{uK,uG,uW} K G}
    (hDA : SmoothRep.IsSubquotient D A) (hA : Subsingleton A) :
    Subsingleton D := by
  obtain ⟨X, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDA
  constructor
  intro d e
  obtain ⟨x, rfl⟩ := hq d
  obtain ⟨y, rfl⟩ := hq e
  exact congrArg (SmoothRep.hom q) (hi (hA.elim _ _))

/-- A glued object with only zero or copies of one irreducible piece has finite
length and all its irreducible actual subquotients occur in that piece. -/
theorem finiteLength_support_of_glued {K : Type uK} [Field K]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {C : Type uC} [Category.{vC} C]
    (M : C ⥤ SmoothRep.{uK,uG,uW} K G)
    {ι : Type uι} [Fintype ι] {P : ι → C ⥤ Rep.{uW} K G}
    (h : IsGluedFromFamily (M ⋙ SmoothRep.toRep) P)
    (X : C) (U : SmoothRep.{uK,uG,uW} K G) (hU : U.IsIrreducible)
    (hP : ∀ i, Subsingleton ((P i).obj X) ∨
      Nonempty (((P i).obj X).ρ.Equiv U.representation)) :
    (M.obj X).HasFiniteLength ∧ SmoothRep.HasConstituentSupportIn (M.obj X) U := by
  constructor
  · apply finiteLength_of_glued h X
    intro i
    apply Module.length_ne_top_iff.mp
    change repLength ((P i).obj X).ρ ≠ ⊤
    rcases hP i with hz | he
    · rw [repLength_eq_zero_iff.mpr hz]
      simp
    · obtain ⟨e⟩ := he
      rw [repLength_congr e, repLength_eq_one_iff.mpr hU]
      simp
  · intro D hD hDX
    obtain ⟨e, σ, s, hs⟩ := h
    let t : ObjectRepFiltration (M.obj X).obj _ := evaluatedFiltration s X
    obtain ⟨j, hj⟩ := t.exists_smoothGradedObject_subquotient hD hDX
    obtain ⟨ej⟩ := hs j
    let eG := (evaluatedGradedEquiv s X j).trans (Representation.equivOfIso (ej.app X))
    rcases hP (e (σ j)) with hz | heU
    · have hz' : Subsingleton (t.smoothGradedObject j) :=
        ⟨fun v w => eG.injective (hz.elim _ _)⟩
      have hDz := subsingleton_of_isSubquotient hj hz'
      have hnt : Nontrivial D := by
        have : IsSimpleModule (MonoidAlgebra K G) D.representation.asModule :=
          (Representation.irreducible_iff_isSimpleModule_asModule _).mp hD
        exact IsSimpleModule.nontrivial (MonoidAlgebra K G) D.representation.asModule
      let : Nontrivial D := hnt
      exact False.elim (not_subsingleton D hDz)
    · obtain ⟨eU⟩ := heU
      exact hj.of_iso_right (SmoothRep.mkIso (eG.trans eU))

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- An equivalence after one rank transport induces the equivalence after
transporting both sides to any common rank. -/
def equiv_rankCast {a b c : ℕ} (hab : a = b) (hac : a = c) (hbc : b = c) :
    letI := T.topology
    ∀ (X : SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
      (Y : SmoothRep.{0,uF,uV} ℂ (GeneralLinear b F.Carrier)),
      ((generalLinearRankCast T hab).obj X).representation.Equiv Y.representation →
      ((generalLinearRankCast T hac).obj X).representation.Equiv
        ((generalLinearRankCast T hbc).obj Y).representation := by
  subst hab hac
  exact fun _ _ e => e

/-- Every feasible order-`2d` grade is zero or equivalent to the transported
upper supercuspidal factor. -/
theorem order_two_d_piece {d : ℕ} (hd : 0 < d)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    ∀ (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
      let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd B.obj A.obj)
      ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
      ∀ x : LeibnizIndex (d + d) d (d + d),
        let G := (leibnizPiece T ψ (d + d) d (d + d) x).obj
          (SmoothRep.quotient P S, A.obj)
        Subsingleton G ∨
          Nonempty (G.ρ.Equiv
            ((generalLinearRankCast T (show d = ((d + d) + d) - (d + d) by omega)).obj
              A.obj).representation) := by
  let := T.topology
  intro B A hAB P S hS₀ hS₁ x
  rcases x with ⟨⟨i, j⟩, hx⟩
  have hx' := mem_leibnizIndices.mp hx
  by_cases hj₀ : j = 0
  · subst j
    obtain rfl : i = d + d := by omega
    right
    obtain ⟨e⟩ := BinaryProductBridge.nonempty_equiv_rankCast_product_left.{uF,max uF uV}
      F T (Nat.sub_self (d + d)) (leibnizIndices_rank hx) (by omega)
      ((generalLinearDerivative T ψ (d + d) (d + d) le_rfl).obj (SmoothRep.quotient P S))
      A.obj
      (TwoSupercuspidalTopDerivatives.increasing_quotient_top.{uF,uV}
        T hd ψ B A hAB S hS₀ hS₁).2
    exact ⟨e.symm⟩
  by_cases hjd : j = d
  · subst j
    have hi : i = d := by omega
    subst i
    right
    have hA := TwoSupercuspidalPartialDerivatives.finrank_topDerivative.{uF,max uF uV}
      T ψ hd A
    change Module.finrank ℂ
      ((generalLinearRankCast T (Nat.sub_self d)).obj
        ((generalLinearDerivative T ψ d d le_rfl).obj A.obj)) = 1 at hA
    rw [TwoSupercuspidalPartialDerivatives.finrank_rankCast] at hA
    obtain ⟨eP⟩ := BinaryProductBridge.nonempty_equiv_rankCast_product_right.{uF,max uF uV}
      F T (Nat.sub_self d) (leibnizIndices_rank hx) (by omega)
      ((generalLinearDerivative T ψ (d + d) d (by omega)).obj (SmoothRep.quotient P S))
      ((generalLinearDerivative T ψ d d le_rfl).obj A.obj) hA
    obtain ⟨eQ⟩ := (twoSupercuspidalAdjacentProductMiddleDerivatives.{uF,max uF uV}
      F T ψ d hd B A (Or.inl hAB) S hS₀ hS₁).2
    let eA := equiv_rankCast T (c := ((d + d) + d) - (d + d))
      (Nat.add_sub_cancel d d) (by omega) (by omega)
      ((generalLinearDerivative T ψ (d + d) d (by omega)).obj (SmoothRep.quotient P S))
      A.obj eQ
    exact ⟨eP.symm.trans eA⟩
  · left
    have hA := SupercuspidalDerivativeVanishing.subsingleton_generalLinearDerivative
      T ψ d j hx'.2.1 (by omega) (by omega) A.obj A.property.2
    exact BinaryProductBridge.subsingleton_rankCast_product.{uF,max uF uV}
      F T (leibnizIndices_rank hx) _ _ (Or.inr hA)

/-- The actual order-`2d` derivative has finite length, and every irreducible
actual subquotient occurs in the transported upper cuspidal factor. -/
theorem order_two_d_finiteLength_support {d : ℕ} (hd : 0 < d)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    ∀ (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
      let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd B.obj A.obj)
      ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
        let R := (generalLinearDerivative T ψ ((d + d) + d) (d + d) (by omega)).obj
          ((T.binaryNormalizedProductFunctor (d + d) d).obj
            (SmoothRep.quotient P S, A.obj))
        let U := (generalLinearRankCast T
          (show d = ((d + d) + d) - (d + d) by omega)).obj A.obj
        R.HasFiniteLength ∧ SmoothRep.HasConstituentSupportIn R U := by
  let := T.topology
  intro B A hAB P S hS₀ hS₁
  let M := T.binaryNormalizedProductFunctor.{uF,max uF uV} (d + d) d ⋙
    generalLinearDerivative T ψ ((d + d) + d) (d + d) (by omega)
  have hglue := AdjacentQuotientUpperProduct.positiveGlued.{uF,max uF uV}
    T (by omega : 0 < d + d) hd ψ (d + d) ⟨by omega, by omega⟩
  exact finiteLength_support_of_glued M hglue (SmoothRep.quotient P S, A.obj) _
    (SupercuspidalTopDerivative.isIrreducible_rankCast T _ A.obj A.property.1)
    (order_two_d_piece.{uF,uV} T hd ψ B A hAB S hS₀ hS₁)

end Langlands.Classification.AdjacentQuotientUpperProductDerivatives

namespace Langlands.Classification

open GeneralLinear Derivative

universe uF uV

/-- Finite length and actual upper-factor constituent support at derivative
order `2d` of a supplied increasing adjacent quotient times its upper factor. -/
def IncreasingAdjacentQuotientUpperProductSecondDerivative
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (d : ℕ) (hd : 0 < d)
    (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
    A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
    let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
      (twoBlockFactors hd hd B.obj A.obj)
    ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
      let R := (generalLinearDerivative T ψ ((d + d) + d) (d + d) (by omega)).obj
        ((T.binaryNormalizedProductFunctor (d + d) d).obj
          (SmoothRep.quotient P S, A.obj))
      let U := (generalLinearRankCast T
        (show d = ((d + d) + d) - (d + d) by omega)).obj A.obj
      R.HasFiniteLength ∧ SmoothRep.HasConstituentSupportIn R U

/-- Actual Leibniz gluing and the supplied-quotient derivative formulas prove
the second common-rank derivative assertion. -/
theorem increasingAdjacentQuotientUpperProductSecondDerivative
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    IncreasingAdjacentQuotientUpperProductSecondDerivative.{uF,uV} F T :=
  fun ψ d hd =>
    AdjacentQuotientUpperProductDerivatives.order_two_d_finiteLength_support.{uF,uV}
      T (d := d) hd ψ

end Langlands.Classification
