import Langlands.Representation.Derivative.LocalPositiveLeibniz
import Langlands.Representation.Classification.TwoSupercuspidalTopDerivatives
import Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge

/-! Derivative calculations for the product of a supplied adjacent quotient
and its upper cuspidal factor. -/

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.AdjacentQuotientUpperProduct

open GeneralLinear Derivative

universe uF uV uR uG uW uC vC uι

/-- A one-step filtration identifies its sole actual quotient with the source. -/
def oneStepGradedIso {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
    {C : Type uC} [Category.{vC} C] {M : C ⥤ Rep.{uW} R G}
    (s : RepFunctorFiltration M 1) :
    s.graded 0 ≅ M := by
  apply (s.step 0).quotientNatIsoOfSurjective (s.step 1) (s.step 1).inclusion
  · intro X v
    change (v : M.obj X) ∈ (s.step 0).obj X ↔ (v : M.obj X) = 0
    rw [s.zero X]
    rfl
  · intro X v
    refine ⟨⟨v, ?_⟩, rfl⟩
    rw [show (s.step 1).obj X = ⊤ from s.top X]
    trivial

/-- Gluing from a one-element family is an actual natural isomorphism. -/
theorem nonempty_iso_of_glued_unique
    {R : Type uR} [CommRing R] {G : Type uG} [Group G]
    {C : Type uC} [Category.{vC} C] {M : C ⥤ Rep.{uW} R G}
    {ι : Type uι} [Fintype ι] [Unique ι] {P : ι → C ⥤ Rep.{uW} R G}
    (h : IsGluedFromFamily M P) (i : ι) :
    Nonempty (M ≅ P i) := by
  obtain ⟨e, σ, s, hs⟩ := h.exists_equiv 1 (Fintype.card_unique)
  obtain ⟨a⟩ := hs 0
  exact ⟨(oneStepGradedIso s).symm ≪≫ a ≪≫
    eqToIso (congrArg P (Subsingleton.elim _ _))⟩

/-- The unique feasible top-order index is the pair of top factor orders. -/
abbrev topIndexUnique (a b : ℕ) : Unique (LeibnizIndex a b (a + b)) where
  default := ⟨(a, b), by simp⟩
  uniq x := by
    apply Subtype.ext
    have hx := x.property
    simpa only [leibnizIndices_top, Finset.mem_singleton] using hx

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The actual positive-rank gluing with arbitrary displayed positive ranks. -/
theorem positiveGlued {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (i : ℕ) (hi : 0 < i ∧ i ≤ a + b) :
    IsGluedFromFamily (leibnizSource.{uF,uV} T ψ a b i hi.2)
      (leibnizPiece T ψ a b i) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt ha)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hb)
  exact LocalPositiveLeibniz.positiveGlued.{uF,uV} T ψ m n i hi

/-- If both top factor derivatives have dimension one, the actual top
derivative of their positive-rank product has dimension one. -/
theorem finrank_product_top {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear b F.Carrier)),
      Module.finrank ℂ ((generalLinearDerivative T ψ a a le_rfl).obj A) = 1 →
      Module.finrank ℂ ((generalLinearDerivative T ψ b b le_rfl).obj B) = 1 →
      Module.finrank ℂ
        ((generalLinearDerivative T ψ (a + b) (a + b) le_rfl).obj
          ((T.binaryNormalizedProductFunctor a b).obj (A, B))) = 1 := by
  let := T.topology
  intro A B hA hB
  let := topIndexUnique a b
  let x : LeibnizIndex a b (a + b) := ⟨(a, b), by simp⟩
  have hglue := positiveGlued.{uF,uV} T ha hb ψ (a + b) ⟨by omega, le_rfl⟩
  obtain ⟨e⟩ := nonempty_iso_of_glued_unique hglue x
  have hdim := (Representation.equivOfIso (e.app (A, B))).toLinearEquiv.finrank_eq
  rw [leibnizSource_obj.{uF,uV} T ψ a b (a + b) le_rfl A B] at hdim
  refine hdim.trans ?_
  rw [leibnizPiece_obj.{uF,uV} T ψ a b (a + b) x A B]
  exact BinaryProductBridge.finrank_rankCast_product_of_zero_zero.{uF,uV} F T
    (Nat.sub_self _) (Nat.sub_self _) (leibnizIndices_rank x.property) _ _ hA hB

/-- A supplied proper increasing-product quotient, multiplied by its upper
cuspidal factor, has one-dimensional actual top derivative. -/
theorem increasing_quotient_upper_product_top {d : ℕ} (hd : 0 < d)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    ∀ (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
      let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd B.obj A.obj)
      ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
        Module.finrank ℂ
          ((generalLinearDerivative T ψ ((d + d) + d) ((d + d) + d) le_rfl).obj
            ((T.binaryNormalizedProductFunctor (d + d) d).obj
              (SmoothRep.quotient P S, A.obj))) = 1 := by
  let := T.topology
  intro B A hAB P S hS₀ hS₁
  have hQ := (TwoSupercuspidalTopDerivatives.increasing_quotient_top.{uF,uV}
    T hd ψ B A hAB S hS₀ hS₁).2
  have hA := TwoSupercuspidalPartialDerivatives.finrank_topDerivative.{uF,max uF uV}
    T ψ hd A
  change Module.finrank ℂ
    ((generalLinearRankCast T (Nat.sub_self d)).obj
      ((generalLinearDerivative T ψ d d le_rfl).obj A.obj)) = 1 at hA
  rw [TwoSupercuspidalPartialDerivatives.finrank_rankCast] at hA
  exact finrank_product_top.{uF,max uF uV} T (by omega) hd ψ
    (SmoothRep.quotient P S) A.obj hQ hA

end Langlands.Classification.AdjacentQuotientUpperProduct

namespace Langlands.Classification

open GeneralLinear Derivative

universe uF uV

/-- Top dimension one for a supplied proper increasing adjacent quotient
multiplied by its upper cuspidal factor. -/
def IncreasingAdjacentQuotientUpperProductTopDerivative
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (d : ℕ) (hd : 0 < d)
    (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
    A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
    let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
      (twoBlockFactors hd hd B.obj A.obj)
    ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
      Module.finrank ℂ
        ((generalLinearDerivative T ψ ((d + d) + d) ((d + d) + d) le_rfl).obj
          ((T.binaryNormalizedProductFunctor (d + d) d).obj
            (SmoothRep.quotient P S, A.obj))) = 1

/-- The actual top-order Leibniz gluing proves top dimension one for the
supplied quotient product. -/
theorem increasingAdjacentQuotientUpperProductTopDerivative
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    IncreasingAdjacentQuotientUpperProductTopDerivative.{uF,uV} F T :=
  fun ψ d hd =>
    AdjacentQuotientUpperProduct.increasing_quotient_upper_product_top.{uF,uV}
      T (d := d) hd ψ

end Langlands.Classification
