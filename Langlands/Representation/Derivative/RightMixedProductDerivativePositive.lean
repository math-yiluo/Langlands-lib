import Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement
import Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
import Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary
import Langlands.Representation.Derivative.MixedProductDerivativeStatement
import Langlands.Representation.Derivative.LevelCalculus
import Langlands.Representation.Filtration.GluedFamily

/-!
# Positive-rank right mixed-product derivative filtration

BZ77 4.14(b) for `GL` rank `k + 1`, by induction on the mirabolic rank. The
4.13(c), 4.14(a) and minus-exactness propositions it needs are explicit
hypotheses.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV uW uC vC uD vD uE vE uι

namespace RightMixedDerivative

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-! ## Exactness of composites and rank transports -/

section Exact

open Mirabolic

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

theorem mapsShortExact_generalLinearRankCast {a b : ℕ} (h : a = b) :
    letI := T.topology
    MapsShortExactIntertwiners (generalLinearRankCast.{uF, uW} T h) := by
  let _ := T.topology
  subst h
  exact LevelCalculus.mapsShortExact_id

end Exact

/-! ## Rank transports and the order recursion

All comparisons are equalities of functors, proved after generalizing the ranks
to variables, so that every rank transport becomes the identity by `subst`. -/

section Casts

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- A mirabolic transport before a derivative of fixed order, compensated after it. -/
theorem derivative_transport {C : Type uC} [Category.{vC} C] {E : Type uE} [Category.{vE} E]
    {a b : ℕ} (h : a = b) (i : ℕ) (ha : 0 < i ∧ i ≤ a + 1) (hb : 0 < i ∧ i ≤ b + 1) {c : ℕ}
    (hc : a + 1 - i = c) (hc' : b + 1 - i = c) :
    letI := T.topology
    ∀ (X : C ⥤ SmoothRep.{0, uF, uW} ℂ (mirabolic a F.Carrier))
      (Z : SmoothRep.{0, uF, uW} ℂ (GeneralLinear c F.Carrier) ⥤ E),
      X ⋙ mirabolicRankCast T h ⋙ mirabolicDerivativeOfOrder T ψ b i hb ⋙
          generalLinearRankCast T hc' ⋙ Z =
        X ⋙ mirabolicDerivativeOfOrder T ψ a i ha ⋙ generalLinearRankCast T hc ⋙ Z := by
  let _ := T.topology
  subst h
  intro X Z
  rfl

/-- A mirabolic transport before a derivative and two `GL` transports after it. -/
theorem castDerivativeCast_eq {C : Type uC} [Category.{vC} C] {E : Type uE} [Category.{vE} E]
    {a b c d : ℕ} (h : a = b) (i : ℕ) (ha : 0 < i ∧ i ≤ a + 1) (hb : 0 < i ∧ i ≤ b + 1)
    (hr : b + 1 - i = d) (h₁ : a + 1 - i = c) (h₂ : c = d) :
    letI := T.topology
    ∀ (X : C ⥤ SmoothRep.{0, uF, uW} ℂ (mirabolic a F.Carrier))
      (Z : SmoothRep.{0, uF, uW} ℂ (GeneralLinear d F.Carrier) ⥤ E),
      X ⋙ mirabolicRankCast T h ⋙ mirabolicDerivativeOfOrder T ψ b i hb ⋙
          generalLinearRankCast T hr ⋙ Z =
        X ⋙ mirabolicDerivativeOfOrder T ψ a i ha ⋙ generalLinearRankCast T h₁ ⋙
          generalLinearRankCast T h₂ ⋙ Z := by
  let _ := T.topology
  subst h h₂
  intro X Z
  rfl

/-- Peeling one `Φ⁻` off a derivative: `Φ⁻ ⋙ D^(i) = D^(i+1)`, up to rank transport. -/
theorem phiMinus_derivative_eq (N i : ℕ) (hi : 0 < i ∧ i ≤ N + 1)
    (hi' : 0 < i + 1 ∧ i + 1 ≤ N + 1 + 1) (hr : N + 1 + 1 - (i + 1) = N + 1 - i) :
    letI := T.topology
    Mirabolic.phiMinus T ψ N ⋙ mirabolicDerivativeOfOrder.{uF, uW} T ψ N i hi =
      mirabolicDerivativeOfOrder T ψ (N + 1) (i + 1) hi' ⋙ generalLinearRankCast T hr := by
  let _ := T.topology
  rcases i with _ | j
  · exact absurd hi.1 (Nat.lt_irrefl 0)
  have key : ∀ (n n' : ℕ) (hn : n = n') (h₁ : N + 1 = n + (j + 1)) (h₂ : N = n' + j),
      Mirabolic.phiMinus T ψ N ⋙
          (mirabolicRankCast T h₂ ⋙ mirabolicDerivative.{uF, uW} T ψ n' j) =
        (mirabolicRankCast T h₁ ⋙ mirabolicDerivative T ψ n (j + 1)) ⋙
          generalLinearRankCast T hn := by
    intro n n' hn h₁ h₂
    subst hn
    subst h₂
    rfl
  exact key _ _ hr (mirabolic_rank_eq_of_order hi') (mirabolic_rank_eq_of_order hi)

/-- The order recursion in the direction used for sources, with a trailing functor. -/
theorem derivative_succ_eq {E : Type uE} [Category.{vE} E] (N i : ℕ)
    (hi : 0 < i ∧ i ≤ N + 1) (hi' : 0 < i + 1 ∧ i + 1 ≤ N + 1 + 1)
    (hr : N + 1 - i = N + 1 + 1 - (i + 1)) :
    letI := T.topology
    ∀ Z : SmoothRep.{0, uF, uW} ℂ (GeneralLinear (N + 1 + 1 - (i + 1)) F.Carrier) ⥤ E,
      mirabolicDerivativeOfOrder.{uF, uW} T ψ (N + 1) (i + 1) hi' ⋙ Z =
        Mirabolic.phiMinus T ψ N ⋙ mirabolicDerivativeOfOrder T ψ N i hi ⋙
          generalLinearRankCast T hr ⋙ Z := by
  let _ := T.topology
  rcases i with _ | j
  · exact absurd hi.1 (Nat.lt_irrefl 0)
  have key : ∀ (n n' : ℕ) (hn : n' = n) (h₁ : N + 1 = n + (j + 1)) (h₂ : N = n' + j)
      (Z : SmoothRep.{0, uF, uW} ℂ (GeneralLinear n F.Carrier) ⥤ E),
      (mirabolicRankCast T h₁ ⋙ mirabolicDerivative.{uF, uW} T ψ n (j + 1)) ⋙ Z =
        Mirabolic.phiMinus T ψ N ⋙
          (mirabolicRankCast T h₂ ⋙ mirabolicDerivative T ψ n' j) ⋙
            generalLinearRankCast T hn ⋙ Z := by
    intro n n' hn h₁ h₂ Z
    subst hn
    subst h₂
    rfl
  exact key _ _ hr (mirabolic_rank_eq_of_order hi') (mirabolic_rank_eq_of_order hi)

/-- Restriction to the mirabolic subgroup followed by its derivative is the `GL`
derivative of the same order. -/
theorem restrictionDerivative_eq (k i : ℕ) (hi : 0 < i ∧ i ≤ k + 1) (hi' : i ≤ k + 1) :
    letI := T.topology
    generalLinearRestriction T k ⋙ mirabolicDerivativeOfOrder.{uF, uW} T ψ k i hi =
      generalLinearDerivative T ψ (k + 1) i hi' := by
  let _ := T.topology
  rcases i with _ | j
  · exact absurd hi.1 (Nat.lt_irrefl 0)
  have key : ∀ (m : ℕ) (h : k = m + j) (h' : k + 1 = m + j + 1),
      generalLinearRestriction T k ⋙
          (mirabolicRankCast T h ⋙ mirabolicDerivative.{uF, uW} T ψ m j) =
        generalLinearRankCast T h' ⋙ generalLinearDerivativePositive T ψ m j := by
    intro m h h'
    subst h
    rfl
  exact key _ (mirabolic_rank_eq_of_order hi) (rank_eq_of_succ_le hi')

/-- A shifted left factor of a binary product, with the rank transports moved. -/
theorem pieceShift_aux {C : Type uC} [Category.{vC} C] {C' : Type uD} [Category.{vD} C']
    {D : Type uE} [Category.{vE} D] {a a' b n m : ℕ}
    (ha : a' = a) (h₁ : a + b = n) (h : n = m) (h₂ : a' + b = m) :
    letI := T.topology
    ∀ (U : C ⥤ C') (X : C' ⥤ SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
      (X' : C ⥤ SmoothRep.{0, uF, uV} ℂ (GeneralLinear a' F.Carrier))
      (Y : D ⥤ SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
      U ⋙ X = X' ⋙ generalLinearRankCast T ha →
      U.prod (𝟭 D) ⋙ (X.prod Y ⋙ T.binaryNormalizedProductFunctor a b ⋙
          generalLinearRankCast T h₁) ⋙ generalLinearRankCast T h ⋙ SmoothRep.toRep =
        X'.prod Y ⋙ T.binaryNormalizedProductFunctor a' b ⋙ generalLinearRankCast T h₂ ⋙
          SmoothRep.toRep := by
  let _ := T.topology
  subst ha h
  intro U X X' Y eX
  have e : (U ⋙ X).prod Y = (X' ⋙ generalLinearRankCast T (rfl : a' = a')).prod Y := by
    rw [eX]
  exact congrArg (fun W => W ⋙ T.binaryNormalizedProductFunctor a' b ⋙
    generalLinearRankCast T h₂ ⋙ SmoothRep.toRep) e

end Casts

/-! ## Gluing transported along a rank cast -/

theorem glued_rankCast (T : F.TopologicalData) {C : Type uC} [Category.{vC} C]
    {ι : Type uι} [Fintype ι] {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ (S : C ⥤ SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier))
      (P : ι → C ⥤ SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier)),
      IsGluedFromFamily (S ⋙ SmoothRep.toRep) (fun i => P i ⋙ SmoothRep.toRep) →
      IsGluedFromFamily (S ⋙ generalLinearRankCast T h ⋙ SmoothRep.toRep)
        (fun i => P i ⋙ generalLinearRankCast T h ⋙ SmoothRep.toRep) := by
  let _ := T.topology
  subst h
  intro S P hS
  exact hS

/-! ## Indices -/

/-- The unique index of order one. -/
abbrev indexOneUnique (k r : ℕ) : Unique (RightMixedDerivativeIndex k r 1) where
  default := ⟨(1, 0), by rw [mem_rightMixedDerivativeIndices]; omega⟩
  uniq := by
    rintro ⟨⟨j, t⟩, hx⟩
    rw [mem_rightMixedDerivativeIndices] at hx
    obtain ⟨rfl, rfl⟩ : j = 1 ∧ t = 0 := by simp only at hx; omega
    rfl

/-- The index `(1, e + 1)` of the quotient term. -/
abbrev quotientIndex (k R e : ℕ) (he : e + 1 ≤ k + 1) :
    RightMixedDerivativeIndex (k + 1) R (e + 2) :=
  ⟨(1, e + 1), by rw [mem_rightMixedDerivativeIndices]; omega⟩

/-- The single index at mirabolic rank zero and order at least two. -/
abbrev indexZeroUnique (k e : ℕ) (he : e + 1 ≤ k + 1) :
    Unique (RightMixedDerivativeIndex (k + 1) 0 (e + 2)) where
  default := quotientIndex k 0 e he
  uniq := by
    rintro ⟨⟨j, t⟩, hx⟩
    rw [mem_rightMixedDerivativeIndices] at hx
    obtain ⟨rfl, rfl⟩ : j = 1 ∧ t = e + 1 := by simp only at hx; omega
    rfl

/-- The shift of the indices of the subobject and the quotient index. -/
def spliceIndexFun (K r e : ℕ) :
    RightMixedDerivativeIndex K r (e + 1) ⊕ PLift (e + 1 ≤ K) →
      RightMixedDerivativeIndex K (r + 1) (e + 2) :=
  Sum.elim
    (fun x => ⟨(x.val.1 + 1, x.val.2), by
      have := mem_rightMixedDerivativeIndices.mp x.property
      rw [mem_rightMixedDerivativeIndices]
      omega⟩)
    (fun h => ⟨(1, e + 1), by
      have := h.down
      rw [mem_rightMixedDerivativeIndices]
      omega⟩)

theorem spliceIndexFun_bijective (K r e : ℕ) : Function.Bijective (spliceIndexFun K r e) := by
  constructor
  · rintro (⟨⟨j, t⟩, hx⟩ | ⟨h⟩) (⟨⟨j', t'⟩, hx'⟩ | ⟨h'⟩) hxy
    · have h1 := congrArg (fun y => y.val.1) hxy
      have h2 := congrArg (fun y => y.val.2) hxy
      simp only [spliceIndexFun, Sum.elim_inl] at h1 h2
      have : j = j' := by omega
      subst this h2
      rfl
    · have h1 := congrArg (fun y => y.val.1) hxy
      have := mem_rightMixedDerivativeIndices.mp hx
      simp only [spliceIndexFun, Sum.elim_inl, Sum.elim_inr] at h1 this
      omega
    · have h1 := congrArg (fun y => y.val.1) hxy
      have := mem_rightMixedDerivativeIndices.mp hx'
      simp only [spliceIndexFun, Sum.elim_inl, Sum.elim_inr] at h1 this
      omega
    · exact congrArg Sum.inr (Subsingleton.elim _ _)
  · rintro ⟨⟨j, t⟩, hy⟩
    have hy' := mem_rightMixedDerivativeIndices.mp hy
    simp only at hy'
    by_cases hj : j = 1
    · subst hj
      obtain rfl : t = e + 1 := by omega
      exact ⟨Sum.inr ⟨by omega⟩, rfl⟩
    · have hj1 : 1 ≤ j := hy'.1
      refine ⟨Sum.inl ⟨(j - 1, t), ?_⟩, ?_⟩
      · rw [mem_rightMixedDerivativeIndices]
        omega
      · apply Subtype.ext
        change (j - 1 + 1, t) = (j, t)
        rw [Nat.sub_add_cancel hj1]

/-- The index equivalence for splicing at mirabolic rank `r + 1`. -/
def spliceIndexEquiv (K r e : ℕ) :
    RightMixedDerivativeIndex K r (e + 1) ⊕ PLift (e + 1 ≤ K) ≃
      RightMixedDerivativeIndex K (r + 1) (e + 2) :=
  Equiv.ofBijective _ (spliceIndexFun_bijective K r e)

/-! ## The three reductions -/

section Reductions

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The source as a composite with `SmoothRep.toRep` last. -/
theorem source_eq_comp (K r d : ℕ) (hd : 0 < d ∧ d ≤ (K + r) + 1) :
    letI := T.topology
    rightMixedDerivativeSource.{uF, uV} T ψ K r d hd =
      (T.rightMixedProductFunctor K r ⋙ mirabolicDerivativeOfOrder T ψ (K + r) d hd) ⋙
        SmoothRep.toRep := by
  let _ := T.topology
  rw [Functor.assoc]
  rfl

/-- The grades as composites with `SmoothRep.toRep` last. -/
theorem piece_eq_comp (K r d : ℕ) :
    letI := T.topology
    rightMixedDerivativePiece.{uF, uV} T ψ K r d = fun x =>
      ((mirabolicDerivativeOfOrder.{uF, uV} T ψ r x.val.1
            (rightMixedDerivativeIndices_left_bound x.property)).prod
          (generalLinearDerivative.{uF, uV} T ψ K x.val.2
            (rightMixedDerivativeIndices_right_le x.property)) ⋙
        T.binaryNormalizedProductFunctor (r + 1 - x.val.1) (K - x.val.2) ⋙
        generalLinearRankCast T (rightMixedDerivativeIndices_rank x.property)) ⋙
      SmoothRep.toRep := by
  let _ := T.topology
  funext x
  simp only [Functor.assoc]
  rfl

/-- The source at order `e + 2` is the order-`(e+1)` derivative of `Φ⁻(τ × ρ)`. -/
theorem source_succ_eq (k r e : ℕ) (hd : 0 < e + 2 ∧ e + 2 ≤ (k + 1 + r) + 1)
    (hq : 0 < e + 1 ∧ e + 1 ≤ k + r + 1)
    (hr : k + r + 1 - (e + 1) = (k + 1 + r) + 1 - (e + 2)) :
    letI := T.topology
    rightMixedDerivativeSource.{uF, uV} T ψ (k + 1) r (e + 2) hd =
      MirabolicProductMinus.rightPhiProduct.{uF, uV} T ψ k r ⋙
        mirabolicDerivativeOfOrder.{uF, max uF uV} T ψ (k + r) (e + 1) hq ⋙
          generalLinearRankCast T hr ⋙ SmoothRep.toRep := by
  let _ := T.topology
  have key : ∀ (a : ℕ) (h : a = k + r + 1) (hd : 0 < e + 2 ∧ e + 2 ≤ a + 1)
      (hr' : k + r + 1 - (e + 1) = a + 1 - (e + 2))
      (X : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
          SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ⥤
        SmoothRep.{0, uF, max uF uV} ℂ (mirabolic a F.Carrier)),
      X ⋙ mirabolicDerivativeOfOrder.{uF, max uF uV} T ψ a (e + 2) hd ⋙ SmoothRep.toRep =
        X ⋙ mirabolicRankCast T h ⋙ Mirabolic.phiMinus T ψ (k + r) ⋙
          mirabolicDerivativeOfOrder T ψ (k + r) (e + 1) hq ⋙ generalLinearRankCast T hr' ⋙
            SmoothRep.toRep := by
    intro a h hd hr' X
    subst h
    exact congrArg (fun W => X ⋙ W)
      (derivative_succ_eq T ψ (k + r) (e + 1) hq hd hr' SmoothRep.toRep)
  show T.rightMixedProductFunctor (k + 1) r ⋙
      mirabolicDerivativeOfOrder.{uF, max uF uV} T ψ (k + 1 + r) (e + 2) hd ⋙ SmoothRep.toRep =
    (T.rightMixedProductFunctor (k + 1) r ⋙ mirabolicRankCast T (Nat.succ_add k r) ⋙
      Mirabolic.phiMinus T ψ (k + r)) ⋙
        mirabolicDerivativeOfOrder.{uF, max uF uV} T ψ (k + r) (e + 1) hq ⋙
          generalLinearRankCast T hr ⋙ SmoothRep.toRep
  simp only [Functor.assoc]
  exact key _ (Nat.succ_add k r) hd hr _

theorem quotient_eq₁ (k R e : ℕ) (hq : 0 < e + 1 ∧ e + 1 ≤ k + R + 1)
    (hq' : 0 < e + 1 ∧ e + 1 ≤ R + k + 1)
    (hr : k + R + 1 - (e + 1) = (k + 1 + R) + 1 - (e + 2))
    (h₃ : R + k + 1 - (e + 1) = R + (k + 1 - (e + 1)))
    (h₆ : R + (k + 1 - (e + 1)) = (k + 1 + R) + 1 - (e + 2)) :
    letI := T.topology
    MirabolicProductMinus.rightPhiQuotient.{uF, uV} T k R ⋙
        mirabolicDerivativeOfOrder T ψ (k + R) (e + 1) hq ⋙ generalLinearRankCast T hr ⋙
          SmoothRep.toRep =
      (Mirabolic.psiMinus T R).prod (generalLinearRestriction T k) ⋙
        (T.leftMixedProductFunctor R k ⋙ mirabolicDerivativeOfOrder T ψ (R + k) (e + 1) hq' ⋙
          generalLinearRankCast T h₃) ⋙ generalLinearRankCast T h₆ ⋙ SmoothRep.toRep := by
  let _ := T.topology
  exact castDerivativeCast_eq T ψ (Nat.add_comm R k) (e + 1) hq' hq hr h₃ h₆
    ((Mirabolic.psiMinus T R).prod (generalLinearRestriction T k) ⋙
      T.leftMixedProductFunctor R k) SmoothRep.toRep

theorem quotient_eq₂ (k R e : ℕ) (he : e + 1 ≤ k + 1)
    (h₆ : R + (k + 1 - (e + 1)) = (k + 1 + R) + 1 - (e + 2)) :
    letI := T.topology
    (Mirabolic.psiMinus T R).prod (generalLinearRestriction T k) ⋙
        ((𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear R F.Carrier))).prod
            (mirabolicDerivativeOfOrder T ψ k (e + 1) ⟨Nat.succ_pos e, he⟩) ⋙
          T.binaryNormalizedProductFunctor R (k + 1 - (e + 1))) ⋙
        generalLinearRankCast T h₆ ⋙ SmoothRep.toRep =
      rightMixedDerivativePiece.{uF, uV} T ψ (k + 1) R (e + 2) (quotientIndex k R e he) := by
  let _ := T.topology
  change _ = (mirabolicDerivativeOfOrder.{uF, uV} T ψ R 1 _).prod
      (generalLinearDerivative.{uF, uV} T ψ (k + 1) (e + 1) _) ⋙ _
  rw [mirabolicDerivativeOfOrder_one,
    ← restrictionDerivative_eq T ψ k (e + 1) ⟨Nat.succ_pos e, he⟩ he]
  rfl

/-- The quotient term `Ψ⁻τ × ρ|P` at order `e + 1` is the grade `τ^(1) × ρ^(e+1)`. -/
def quotientIso (hLI : LeftMixedProductDerivativeIso.{uF, uV} F T) (k R e : ℕ)
    (he : e + 1 ≤ k + 1) (hq : 0 < e + 1 ∧ e + 1 ≤ k + R + 1)
    (hr : k + R + 1 - (e + 1) = (k + 1 + R) + 1 - (e + 2)) :
    letI := T.topology
    MirabolicProductMinus.rightPhiQuotient.{uF, uV} T k R ⋙
        mirabolicDerivativeOfOrder T ψ (k + R) (e + 1) hq ⋙ generalLinearRankCast T hr ⋙
          SmoothRep.toRep ≅
      rightMixedDerivativePiece T ψ (k + 1) R (e + 2) (quotientIndex k R e he) := by
  letI := T.topology
  have h₆ : R + (k + 1 - (e + 1)) = (k + 1 + R) + 1 - (e + 2) := by omega
  exact eqToIso (quotient_eq₁.{uF, uV} T ψ k R e hq (by omega) hr (by omega) h₆) ≪≫
    Functor.isoWhiskerLeft
      ((Mirabolic.psiMinus.{uV, uF} T R).prod (generalLinearRestriction.{uF, uV} T k))
      (Functor.isoWhiskerRight (Classical.choice (hLI ψ R k (e + 1) ⟨Nat.succ_pos e, he⟩))
        (generalLinearRankCast T h₆ ⋙ SmoothRep.toRep)) ≪≫
    eqToIso (quotient_eq₂.{uF, uV} T ψ k R e he h₆)

/-- A rank transport of a derivative preserves zero carriers. -/
theorem derivativeCast_subsingleton {a b c : ℕ} (h : a = b) (i : ℕ) (ha : 0 < i ∧ i ≤ a + 1)
    (hb : 0 < i ∧ i ≤ b + 1) (hc : b + 1 - i = c) :
    letI := T.topology
    ∀ Y : SmoothRep.{0, uF, uW} ℂ (mirabolic a F.Carrier),
      Subsingleton ((mirabolicDerivativeOfOrder T ψ a i ha).obj Y) →
      Subsingleton ((generalLinearRankCast T hc).obj
        ((mirabolicDerivativeOfOrder T ψ b i hb).obj ((mirabolicRankCast T h).obj Y))) := by
  let _ := T.topology
  subst h hc
  intro Y hY
  exact hY

/-- Beyond the `GL` rank the quotient term has zero carriers. -/
theorem quotient_subsingleton (hLV : LeftMixedProductDerivativeVanishing.{uF, uV} F T)
    (k R e : ℕ) (he : ¬ e + 1 ≤ k + 1) (hq : 0 < e + 1 ∧ e + 1 ≤ k + R + 1)
    (hr : k + R + 1 - (e + 1) = (k + 1 + R) + 1 - (e + 2)) :
    letI := T.topology
    ∀ X, Subsingleton ((MirabolicProductMinus.rightPhiQuotient.{uF, uV} T k R ⋙
        mirabolicDerivativeOfOrder T ψ (k + R) (e + 1) hq ⋙ generalLinearRankCast T hr ⋙
          SmoothRep.toRep).obj X) := by
  let _ := T.topology
  intro X
  have hq' : 0 < e + 1 ∧ e + 1 ≤ R + k + 1 := by omega
  have h0 := hLV ψ R k (e + 1) hq' (by omega) ((Mirabolic.psiMinus T R).obj X.1)
    ((generalLinearRestriction T k).obj X.2)
  exact derivativeCast_subsingleton T ψ (Nat.add_comm R k) (e + 1) hq' hq hr _ h0

/-- The subobject term `Φ⁻τ × ρ` at order `e + 1` is a precomposed source. -/
theorem sub_eq (k r e : ℕ) (hq : 0 < e + 1 ∧ e + 1 ≤ k + (r + 1) + 1)
    (hr : k + (r + 1) + 1 - (e + 1) = (k + 1 + (r + 1)) + 1 - (e + 2))
    (hd' : 0 < e + 1 ∧ e + 1 ≤ (k + 1 + r) + 1)
    (hc : (k + 1 + r) + 1 - (e + 1) = (k + 1 + (r + 1)) + 1 - (e + 2)) :
    letI := T.topology
    MirabolicProductMinus.rightPhiSubobject.{uF, uV} T ψ k r ⋙
        mirabolicDerivativeOfOrder.{uF, max uF uV} T ψ (k + (r + 1)) (e + 1) hq ⋙
          generalLinearRankCast T hr ⋙ SmoothRep.toRep =
      (Mirabolic.phiMinus T ψ r).prod
          (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))) ⋙
        (T.rightMixedProductFunctor (k + 1) r ⋙
          mirabolicDerivativeOfOrder T ψ (k + 1 + r) (e + 1) hd') ⋙
          generalLinearRankCast T hc ⋙ SmoothRep.toRep := by
  let _ := T.topology
  show ((Mirabolic.phiMinus T ψ r).prod
        (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))) ⋙
      T.rightMixedProductFunctor (k + 1) r) ⋙
      mirabolicRankCast T (Nat.succ_add k r : k + 1 + r = k + (r + 1)) ⋙
      mirabolicDerivativeOfOrder.{uF, max uF uV} T ψ (k + (r + 1)) (e + 1) hq ⋙
        generalLinearRankCast T hr ⋙ SmoothRep.toRep =
    ((Mirabolic.phiMinus T ψ r).prod
        (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))) ⋙
      T.rightMixedProductFunctor (k + 1) r) ⋙
      mirabolicDerivativeOfOrder T ψ (k + 1 + r) (e + 1) hd' ⋙
        generalLinearRankCast T hc ⋙ SmoothRep.toRep
  exact derivative_transport T ψ (Nat.succ_add k r : k + 1 + r = k + (r + 1)) (e + 1) hd' hq
    hc hr _ _

/-- A precomposed grade of the subobject is a shifted grade of the source. -/
theorem pieceShift_eq (k r e : ℕ)
    (hc : (k + 1 + r) + 1 - (e + 1) = (k + 1 + (r + 1)) + 1 - (e + 2))
    (x : RightMixedDerivativeIndex (k + 1) r (e + 1)) :
    letI := T.topology
    (Mirabolic.phiMinus T ψ r).prod
        (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))) ⋙
        ((mirabolicDerivativeOfOrder.{uF, uV} T ψ r x.val.1
            (rightMixedDerivativeIndices_left_bound x.property)).prod
          (generalLinearDerivative.{uF, uV} T ψ (k + 1) x.val.2
            (rightMixedDerivativeIndices_right_le x.property)) ⋙
          T.binaryNormalizedProductFunctor (r + 1 - x.val.1) (k + 1 - x.val.2) ⋙
          generalLinearRankCast T (rightMixedDerivativeIndices_rank x.property)) ⋙
        generalLinearRankCast T hc ⋙ SmoothRep.toRep =
      rightMixedDerivativePiece.{uF, uV} T ψ (k + 1) (r + 1) (e + 2)
        (spliceIndexEquiv (k + 1) r e (Sum.inl x)) := by
  let _ := T.topology
  have hj := rightMixedDerivativeIndices_left_bound x.property
  have hj' : 0 < x.val.1 + 1 ∧ x.val.1 + 1 ≤ r + 1 + 1 := by omega
  have hrr : r + 1 + 1 - (x.val.1 + 1) = r + 1 - x.val.1 := by omega
  exact pieceShift_aux T hrr _ hc
    (rightMixedDerivativeIndices_rank (spliceIndexEquiv (k + 1) r e (Sum.inl x)).property)
    _ _ _ _ (phiMinus_derivative_eq T ψ r x.val.1 hj hj' hrr)

end Reductions

/-! ## The induction -/

section Induction

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

theorem source_one_eq (k r : ℕ) (hd : 0 < 1 ∧ 1 ≤ (k + 1 + r) + 1) :
    letI := T.topology
    rightMixedDerivativeSource.{uF, uV} T ψ (k + 1) r 1 hd =
      (T.rightMixedProductFunctor (k + 1) r ⋙ Mirabolic.psiMinus T ((k + 1) + r)) ⋙
        SmoothRep.toRep := by
  let _ := T.topology
  change T.rightMixedProductFunctor (k + 1) r ⋙ mirabolicDerivativeOfOrder T ψ _ 1 hd ⋙
    SmoothRep.toRep = _
  rw [mirabolicDerivativeOfOrder_one]
  rfl

theorem piece_one_eq (k r : ℕ) :
    letI := T.topology
    rightMixedDerivativePiece.{uF, uV} T ψ (k + 1) r 1 (indexOneUnique (k + 1) r).default =
      ((Mirabolic.psiMinus T r).prod
          (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))) ⋙
        T.binaryNormalizedProductFunctor r (k + 1) ⋙
          generalLinearRankCast T (Nat.add_comm r (k + 1))) ⋙ SmoothRep.toRep := by
  let _ := T.topology
  change (mirabolicDerivativeOfOrder.{uF, uV} T ψ r 1 _).prod
      (generalLinearDerivative.{uF, uV} T ψ (k + 1) 0 _) ⋙
    _ = _
  rw [mirabolicDerivativeOfOrder_one]
  rfl

theorem glued_one (hPsi : MirabolicProductMinus.RightPsiCompatibility.{uF, uV} F T)
    (k r : ℕ) (hd : 0 < 1 ∧ 1 ≤ (k + 1 + r) + 1) :
    IsGluedFromFamily (rightMixedDerivativeSource.{uF, uV} T ψ (k + 1) r 1 hd)
      (rightMixedDerivativePiece T ψ (k + 1) r 1) := by
  let _ := T.topology
  let _ := indexOneUnique (k + 1) r
  obtain ⟨e⟩ := hPsi k r
  exact IsGluedFromFamily.of_iso_unique (eqToIso (source_one_eq T ψ k r hd) ≪≫
    Functor.isoWhiskerRight e SmoothRep.toRep ≪≫ eqToIso (piece_one_eq T ψ k r).symm)

theorem glued_zero (hLI : LeftMixedProductDerivativeIso.{uF, uV} F T)
    (k e : ℕ) (hd : 0 < e + 2 ∧ e + 2 ≤ (k + 1 + 0) + 1) :
    IsGluedFromFamily (rightMixedDerivativeSource.{uF, uV} T ψ (k + 1) 0 (e + 2) hd)
      (rightMixedDerivativePiece T ψ (k + 1) 0 (e + 2)) := by
  let _ := T.topology
  have he : e + 1 ≤ k + 1 := by omega
  have hq : 0 < e + 1 ∧ e + 1 ≤ k + 0 + 1 := by omega
  have hr : k + 0 + 1 - (e + 1) = (k + 1 + 0) + 1 - (e + 2) := by omega
  let _ := indexZeroUnique k e he
  obtain ⟨b⟩ := MirabolicProductMinus.rightPhiBoundary.{uF, uV} T ψ k
  exact IsGluedFromFamily.of_iso_unique (eqToIso (source_succ_eq.{uF, uV} T ψ k 0 e hd hq hr) ≪≫
    Functor.isoWhiskerRight b
      (mirabolicDerivativeOfOrder.{uF, max uF uV} T ψ (k + 0) (e + 1) hq ⋙
        generalLinearRankCast T hr ⋙ SmoothRep.toRep) ≪≫
    quotientIso.{uF, uV} T ψ hLI k 0 e he hq hr)

theorem glued_succ (hSE : MirabolicProductMinus.RightPhiShortExact.{uF, uV} F T)
    (hLI : LeftMixedProductDerivativeIso.{uF, uV} F T)
    (hLV : LeftMixedProductDerivativeVanishing.{uF, uV} F T)
    (hE : Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T)
    (k r e : ℕ) (hd : 0 < e + 2 ∧ e + 2 ≤ (k + 1 + (r + 1)) + 1)
    (hd' : 0 < e + 1 ∧ e + 1 ≤ (k + 1 + r) + 1)
    (ih : IsGluedFromFamily (rightMixedDerivativeSource.{uF, uV} T ψ (k + 1) r (e + 1) hd')
      (rightMixedDerivativePiece T ψ (k + 1) r (e + 1))) :
    IsGluedFromFamily (rightMixedDerivativeSource.{uF, uV} T ψ (k + 1) (r + 1) (e + 2) hd)
      (rightMixedDerivativePiece T ψ (k + 1) (r + 1) (e + 2)) := by
  let _ := T.topology
  have hq : 0 < e + 1 ∧ e + 1 ≤ k + (r + 1) + 1 := by omega
  have hr : k + (r + 1) + 1 - (e + 1) = (k + 1 + (r + 1)) + 1 - (e + 2) := by omega
  have hc : (k + 1 + r) + 1 - (e + 1) = (k + 1 + (r + 1)) + 1 - (e + 2) := by omega
  have hJ : Mirabolic.MapsShortExactIntertwiners
      (mirabolicDerivativeOfOrder.{uF, max uF uV} T ψ (k + (r + 1)) (e + 1) hq ⋙
        generalLinearRankCast T hr) :=
    LevelCalculus.mapsShortExact_comp (LevelCalculus.mapsShortExact_mirabolicDerivativeOfOrder T ψ hE _ _ _)
      (mapsShortExact_generalLinearRankCast T hr)
  obtain ⟨i, q, hiq⟩ := hSE ψ k r
  -- The subobject, from the induction hypothesis.
  rw [source_eq_comp, piece_eq_comp] at ih
  have hL : IsGluedFromFamily
      (MirabolicProductMinus.rightPhiSubobject.{uF, uV} T ψ k r ⋙
        mirabolicDerivativeOfOrder.{uF, max uF uV} T ψ (k + (r + 1)) (e + 1) hq ⋙
          generalLinearRankCast T hr ⋙ SmoothRep.toRep)
      (fun x : RightMixedDerivativeIndex (k + 1) r (e + 1) =>
        rightMixedDerivativePiece.{uF, uV} T ψ (k + 1) (r + 1) (e + 2)
          (spliceIndexEquiv (k + 1) r e (Sum.inl x))) :=
    (((glued_rankCast T hc _ _ ih).precomp
        ((Mirabolic.phiMinus T ψ r).prod
          (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))))).isoPieces
      (fun x => eqToIso (pieceShift_eq.{uF, uV} T ψ k r e hc x))).iso
      (eqToIso (sub_eq.{uF, uV} T ψ k r e hq hr hd' hc).symm)
  -- The quotient, from 4.14(a).
  have hQ : IsGluedFromFamily
      (MirabolicProductMinus.rightPhiQuotient.{uF, uV} T k (r + 1) ⋙
        mirabolicDerivativeOfOrder.{uF, max uF uV} T ψ (k + (r + 1)) (e + 1) hq ⋙
          generalLinearRankCast T hr ⋙ SmoothRep.toRep)
      (fun h : PLift (e + 1 ≤ k + 1) =>
        rightMixedDerivativePiece.{uF, uV} T ψ (k + 1) (r + 1) (e + 2)
          (spliceIndexEquiv (k + 1) r e (Sum.inr h))) := by
    by_cases he : e + 1 ≤ k + 1
    · let _ : Unique (PLift (e + 1 ≤ k + 1)) := ⟨⟨⟨he⟩⟩, fun _ => rfl⟩
      exact IsGluedFromFamily.of_iso_unique (quotientIso.{uF, uV} T ψ hLI k (r + 1) e he hq hr)
    · let _ : IsEmpty (PLift (e + 1 ≤ k + 1)) := ⟨fun h => he h.down⟩
      exact IsGluedFromFamily.of_isEmpty
        (quotient_subsingleton.{uF, uV} T ψ hLV k (r + 1) e he hq hr)
  have hM := hL.splice hQ
    (Functor.whiskerRight i
      (mirabolicDerivativeOfOrder.{uF, max uF uV} T ψ (k + (r + 1)) (e + 1) hq ⋙
        generalLinearRankCast T hr ⋙ SmoothRep.toRep))
    (Functor.whiskerRight q
      (mirabolicDerivativeOfOrder.{uF, max uF uV} T ψ (k + (r + 1)) (e + 1) hq ⋙
        generalLinearRankCast T hr ⋙ SmoothRep.toRep))
    (fun X => (hJ _ _ _ (i.app X) (q.app X) (hiq X).1 (hiq X).2.2 (hiq X).2.1).2.1)
    (fun X => (hJ _ _ _ (i.app X) (q.app X) (hiq X).1 (hiq X).2.2 (hiq X).2.1).1)
    (fun X => (hJ _ _ _ (i.app X) (q.app X) (hiq X).1 (hiq X).2.2 (hiq X).2.1).2.2)
  refine (hM.equiv (spliceIndexEquiv (k + 1) r e) ?_).iso
    (eqToIso (source_succ_eq.{uF, uV} T ψ k (r + 1) e hd hq hr).symm)
  rintro (x | h)
  · exact Iso.refl _
  · exact Iso.refl _

/-- BZ77 4.14(b) at positive `GL` rank, from the listed clauses. -/
theorem glued_pos (hPsi : MirabolicProductMinus.RightPsiCompatibility.{uF, uV} F T)
    (hSE : MirabolicProductMinus.RightPhiShortExact.{uF, uV} F T)
    (hLI : LeftMixedProductDerivativeIso.{uF, uV} F T)
    (hLV : LeftMixedProductDerivativeVanishing.{uF, uV} F T)
    (hE : Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T) (k : ℕ) :
    ∀ (r d : ℕ) (hd : 0 < d ∧ d ≤ (k + 1 + r) + 1),
      IsGluedFromFamily (rightMixedDerivativeSource.{uF, uV} T ψ (k + 1) r d hd)
        (rightMixedDerivativePiece T ψ (k + 1) r d) := by
  intro r
  induction r with
  | zero =>
    intro d hd
    rcases d with _ | _ | e
    · omega
    · exact glued_one T ψ hPsi k 0 hd
    · exact glued_zero T ψ hLI k e hd
  | succ r ih =>
    intro d hd
    rcases d with _ | _ | e
    · omega
    · exact glued_one T ψ hPsi k (r + 1) hd
    · exact glued_succ T ψ hSE hLI hLV hE k r e hd (by omega) (ih (e + 1) (by omega))

/-- BZ77 4.14(b) at positive `GL` rank in the shape of the published statement. -/
theorem filtration_pos (hPsi : MirabolicProductMinus.RightPsiCompatibility.{uF, uV} F T)
    (hSE : MirabolicProductMinus.RightPhiShortExact.{uF, uV} F T)
    (hLI : LeftMixedProductDerivativeIso.{uF, uV} F T)
    (hLV : LeftMixedProductDerivativeVanishing.{uF, uV} F T)
    (hE : Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T)
    (k r d : ℕ) (hd : 0 < d ∧ d ≤ (k + 1 + r) + 1) :
    ∃ e : Fin (rightMixedDerivativeIndices (k + 1) r d).card ≃
        RightMixedDerivativeIndex (k + 1) r d,
      IsGluedFrom (rightMixedDerivativeSource.{uF, uV} T ψ (k + 1) r d hd)
        (fun i => rightMixedDerivativePiece T ψ (k + 1) r d (e i)) :=
  (glued_pos T ψ hPsi hSE hLI hLV hE k r d hd).exists_equiv _ (Fintype.card_coe _)

end Induction

end RightMixedDerivative

end Langlands.Derivative
