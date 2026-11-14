import Langlands.AllFieldBZ.Representation.Derivative.Iteration
import Langlands.Representation.Derivative.Homogeneity

/-!
# All-field port of `Langlands.Representation.Derivative.Homogeneity`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.Homogeneity` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis
universe uF uV

variable {F : LocalFieldPackage.{uF}}

/-- Equality transport between actual mirabolic representation categories. -/
def mirabolicRankCast (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (mirabolic b F.Carrier) := by
  letI := T.topology
  exact Eq.rec (motive := fun c _ =>
      SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier) ⥤
        SmoothRep.{0, uF, uV} ℂ (mirabolic c F.Carrier)) (𝟭 _) h

theorem mirabolicRankCast_refl (T : F.TopologicalData) (a : ℕ) (h : a = a) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T h =
      𝟭 (SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier)) :=
  rfl

theorem mirabolicRankCast_obj_subsingleton (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier),
      Subsingleton A → Subsingleton ((mirabolicRankCast T h).obj A) := by
  subst h
  exact fun _ hA => hA

/-- The actual derivative of order `k` on `P_(N+1)`, landing in `GL_(N+1-k)`. -/
def mirabolicDerivativeOfOrder (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N k : ℕ) (hk : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1 - k) F.Carrier) := by
  letI := T.topology
  exact mirabolicRankCast T (mirabolic_rank_eq_of_order hk) ⋙
    mirabolicDerivative T ψ (N + 1 - k) (k - 1)

theorem mirabolicDerivativeOfOrder_eq (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N k : ℕ) (hk : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    mirabolicDerivativeOfOrder.{uF, uV} T ψ N k hk =
      mirabolicRankCast T (mirabolic_rank_eq_of_order hk) ⋙
        mirabolicDerivative T ψ (N + 1 - k) (k - 1) :=
  rfl

theorem mirabolicDerivativeOfOrder_obj (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N k : ℕ) (hk : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      (mirabolicDerivativeOfOrder T ψ N k hk).obj A =
        (mirabolicDerivative T ψ (N + 1 - k) (k - 1)).obj
          ((mirabolicRankCast T (mirabolic_rank_eq_of_order hk)).obj A) := by
  intros
  rfl

/-- Order one is the published `Ψ⁻`, including when `N = 0`. -/
theorem mirabolicDerivativeOfOrder_one (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N : ℕ) (hk : 0 < 1 ∧ 1 ≤ N + 1) :
    letI := T.topology
    mirabolicDerivativeOfOrder.{uF, uV} T ψ N 1 hk = Mirabolic.psiMinus T N := by
  let _ := T.topology
  exact (Functor.id_comp _).trans (mirabolicDerivative_zero T ψ N)

/-- The top derivative lands in `GL₀` after the explicit target-rank transport. -/
theorem mirabolicDerivativeOfOrder_top (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N : ℕ) (hk : 0 < N + 1 ∧ N + 1 ≤ N + 1) :
    letI := T.topology
    mirabolicDerivativeOfOrder.{uF, uV} T ψ N (N + 1) hk ⋙
        generalLinearRankCast T (Nat.sub_self (N + 1)) =
      mirabolicRankCast T (Nat.zero_add N).symm ⋙ mirabolicDerivative T ψ 0 N := by
  let _ := T.topology
  have key : ∀ (m : ℕ) (hm : m = 0) (h : N = m + N),
      mirabolicRankCast.{uF, uV} T h ⋙ mirabolicDerivative T ψ m N ⋙
          generalLinearRankCast T hm =
        mirabolicRankCast T (Nat.zero_add N).symm ⋙ mirabolicDerivative T ψ 0 N := by
    intro m hm h
    subst hm
    exact congrArg (mirabolicRankCast T h ⋙ ·) (Functor.comp_id _)
  exact key (N + 1 - (N + 1)) (Nat.sub_self (N + 1)) (mirabolic_rank_eq_of_order hk)

/-- Nontriviality is only tested at actual valid derivative orders. -/
def HasNonzeroDerivative (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {N : ℕ} :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier) → ℕ → Prop := by
  letI := T.topology
  exact fun A k => ∃ hk : 0 < k ∧ k ≤ N + 1,
    Nontrivial ((mirabolicDerivativeOfOrder T ψ N k hk).obj A)

theorem hasNonzeroDerivative_iff (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {N k : ℕ} (hk : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      HasNonzeroDerivative T ψ A k ↔
        Nontrivial ((mirabolicDerivativeOfOrder T ψ N k hk).obj A) := by
  intro A
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hk, h⟩⟩

/-- Greatest nonzero derivative order in `1,…,N+1`, defaulting to zero. -/
def level (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {N : ℕ} :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier) → ℕ := by
  letI := T.topology
  classical
  exact fun A => Nat.findGreatest (HasNonzeroDerivative T ψ A) (N + 1)

theorem level_le (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {N : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier), level T ψ A ≤ N + 1 := by
  intro A
  classical
  exact Nat.findGreatest_le (N + 1)

/-- The finite-maximum characterization at a positive order. -/
theorem level_eq_iff (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {N k : ℕ} (hpos : 0 < k) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      level T ψ A = k ↔ k ≤ N + 1 ∧ HasNonzeroDerivative T ψ A k ∧
        ∀ ⦃j⦄, k < j → j ≤ N + 1 → ¬ HasNonzeroDerivative T ψ A j := by
  intro A
  classical
  simpa [level, Nat.ne_of_gt hpos] using
    (Nat.findGreatest_eq_iff (P := HasNonzeroDerivative T ψ A) (k := N + 1) (m := k))

theorem le_level_of_hasNonzeroDerivative (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {N k : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      HasNonzeroDerivative T ψ A k → k ≤ level T ψ A := by
  intro A h
  classical
  exact Nat.le_findGreatest h.choose.2 h

theorem level_eq_zero_iff (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {N : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      level T ψ A = 0 ↔ ∀ k (hk : 0 < k ∧ k ≤ N + 1),
        ¬ Nontrivial ((mirabolicDerivativeOfOrder T ψ N k hk).obj A) := by
  intro A
  classical
  change Nat.findGreatest (HasNonzeroDerivative T ψ A) (N + 1) = 0 ↔ _
  rw [Nat.findGreatest_eq_zero_iff]
  constructor
  · intro h k hk hn
    exact h hk.1 hk.2 ⟨hk, hn⟩
  · intro h k hpos hle hn
    exact h k ⟨hpos, hle⟩ ((hasNonzeroDerivative_iff T ψ ⟨hpos, hle⟩ A).mp hn)

private theorem _root_.Langlands.Derivative.subsingleton_of_surjective {α β : Type*} [Subsingleton α]
    (f : α → β) (hf : Function.Surjective f) : Subsingleton β := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := hf x
  obtain ⟨b, rfl⟩ := hf y
  exact congrArg f (Subsingleton.elim a b)

/-- Each actual quotient step preserves a zero carrier, independently of exactness. -/
theorem phiMinusIterate_obj_subsingleton (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + k) F.Carrier),
      Subsingleton A → Subsingleton ((phiMinusIterate T ψ n k).obj A) := by
  let _ := T.topology
  induction k with
  | zero => exact fun _ hA => hA
  | succ k ih =>
    intro A hA
    let _ := hA
    apply ih ((Mirabolic.phiMinus T ψ (n + k)).obj A)
    exact subsingleton_of_surjective _ (Mirabolic.phiMinusQuotient_surjective T ψ (n + k) A)

theorem mirabolicDerivative_obj_subsingleton (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + k) F.Carrier),
      Subsingleton A → Subsingleton ((mirabolicDerivative T ψ n k).obj A) := by
  let _ := T.topology
  intro A hA
  let _ := phiMinusIterate_obj_subsingleton T ψ n k A hA
  exact subsingleton_of_surjective _
    (Mirabolic.psiMinusQuotient_surjective T n ((phiMinusIterate T ψ n k).obj A))

theorem mirabolicDerivativeOfOrder_obj_subsingleton (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N k : ℕ) (hk : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      Subsingleton A → Subsingleton ((mirabolicDerivativeOfOrder T ψ N k hk).obj A) := by
  intro A hA
  exact mirabolicDerivative_obj_subsingleton T ψ (N + 1 - k) (k - 1)
    ((mirabolicRankCast T (mirabolic_rank_eq_of_order hk)).obj A)
    (mirabolicRankCast_obj_subsingleton T (mirabolic_rank_eq_of_order hk) A hA)

/-- A zero carrier has level zero. This uses surjectivity of actual quotient maps. -/
theorem level_eq_zero_of_subsingleton (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {N : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      Subsingleton A → level T ψ A = 0 := by
  intro A hA
  rw [level_eq_zero_iff T ψ A]
  intro k hk hn
  have hs := mirabolicDerivativeOfOrder_obj_subsingleton T ψ N k hk A hA
  obtain ⟨x, y, hxy⟩ := hn.exists_pair_ne
  exact hxy (hs.elim x y)

/-- Every nonzero actual invariant subspace has the ambient representation's level. -/
def IsHomogeneous (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {N : ℕ} :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier) → Prop := by
  letI := T.topology
  exact fun A => ∀ U : Subrepresentation A.representation,
    U ≠ ⊥ → level T ψ (SmoothRep.subrepresentation A U) = level T ψ A

/-- Homogeneity of a zero carrier is vacuous: every invariant subspace is bottom. -/
theorem isHomogeneous_of_subsingleton (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {N : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      Subsingleton A → IsHomogeneous T ψ A := by
  let _ := T.topology
  intro A hA U hU
  apply False.elim (hU _)
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · intro v _
    change v = 0
    exact hA.elim v 0
  · exact bot_le

end Langlands.AllFieldBZ.Derivative
