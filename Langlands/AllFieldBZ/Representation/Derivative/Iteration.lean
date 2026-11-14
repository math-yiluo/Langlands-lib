import Langlands.AllFieldBZ.Representation.Derivative.MirabolicMinus
import Langlands.Representation.Derivative.Iteration

/-!
# All-field port of `Langlands.Representation.Derivative.Iteration`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.Iteration` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap mirabolicDerivative mirabolicDerivative_eq mirabolicDerivative_succ mirabolicDerivative_zero phiMinusIterate phiMinusIterate_succ phiMinusIterate_zero
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis
universe uF uV

variable {F : LocalFieldPackage.{uF}}

/-! ## Iterated Phi-minus -/

/-- `(Φ⁻)^k : P_(n+k+1) → P_(n+1)`, applying `Φ⁻` at the largest rank first. -/
def phiMinusIterate (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    (k : ℕ) →
      letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic (n + k) F.Carrier) ⥤
        SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)
  | 0 => letI := T.topology; 𝟭 _
  | k + 1 => letI := T.topology; Mirabolic.phiMinus T ψ (n + k) ⋙ phiMinusIterate T ψ n k

theorem phiMinusIterate_zero (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    phiMinusIterate T ψ n 0 = 𝟭 (SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) :=
  rfl

theorem phiMinusIterate_succ (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    phiMinusIterate.{uF, uV} T ψ n (k + 1) =
      Mirabolic.phiMinus T ψ (n + k) ⋙ phiMinusIterate T ψ n k :=
  rfl

/-! ## Mirabolic derivatives -/

/-- The mirabolic derivative of order `k + 1`, `Ψ⁻ ∘ (Φ⁻)^k : P_(n+k+1) → GL_n`. -/
def mirabolicDerivative (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic (n + k) F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) := by
  letI := T.topology
  exact phiMinusIterate T ψ n k ⋙ Mirabolic.psiMinus T n

theorem mirabolicDerivative_eq (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    mirabolicDerivative.{uF, uV} T ψ n k = phiMinusIterate T ψ n k ⋙ Mirabolic.psiMinus T n :=
  rfl

/-- The first mirabolic derivative is `Ψ⁻`. -/
theorem mirabolicDerivative_zero (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    mirabolicDerivative.{uF, uV} T ψ n 0 = Mirabolic.psiMinus T n :=
  Functor.id_comp _

theorem mirabolicDerivative_succ (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    mirabolicDerivative.{uF, uV} T ψ n (k + 1) =
      Mirabolic.phiMinus T ψ (n + k) ⋙ mirabolicDerivative T ψ n k :=
  Functor.assoc _ _ _

/-! ## Restriction from `GL_(n+1)` to the mirabolic subgroup -/

/-- Restriction along the actual continuous inclusion `P_(n+1) ≤ GL_(n+1)`. -/
def generalLinearRestriction (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) := by
  letI := T.topology
  exact Mirabolic.continuousPullbackFunctor (mirabolic n F.Carrier).subtype
    continuous_subtype_val

/-- Restriction keeps the underlying linear map of every morphism. -/
theorem generalLinearRestriction_map_toLinearMap (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)} (f : A ⟶ B),
      (SmoothRep.hom ((generalLinearRestriction T n).map f)).toLinearMap =
        (SmoothRep.hom f).toLinearMap := by
  intros
  rfl

theorem generalLinearRestriction_map_apply (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)} (f : A ⟶ B) (v : A),
      SmoothRep.hom ((generalLinearRestriction T n).map f) v = SmoothRep.hom f v := by
  intros
  rfl

/-! ## Positive-order `GL` derivatives -/

/-- The `GL` derivative of order `k + 1`, `GL_(n+k+1) → GL_n`. -/
def generalLinearDerivativePositive (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + k + 1) F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) := by
  letI := T.topology
  exact generalLinearRestriction T (n + k) ⋙ mirabolicDerivative T ψ n k

theorem generalLinearDerivativePositive_eq (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    generalLinearDerivativePositive.{uF, uV} T ψ n k =
      generalLinearRestriction T (n + k) ⋙ mirabolicDerivative T ψ n k :=
  rfl

theorem generalLinearDerivativePositive_obj (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + k + 1) F.Carrier),
      (generalLinearDerivativePositive T ψ n k).obj A =
        (mirabolicDerivative T ψ n k).obj ((generalLinearRestriction T (n + k)).obj A) := by
  intros
  rfl

/-! ## Rank transport -/

/-- Transport between the `GL` categories of two provably equal ranks. -/
def generalLinearRankCast (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier) := by
  letI := T.topology
  exact Eq.rec (motive := fun c _ =>
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ⥤
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear c F.Carrier))
    (𝟭 _) h

/-- Any proof of `a = a` gives the identity functor. -/
theorem generalLinearRankCast_refl (T : F.TopologicalData) (a : ℕ) (h : a = a) :
    letI := T.topology
    generalLinearRankCast.{uF, uV} T h =
      𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)) :=
  rfl

theorem generalLinearRankCast_trans (T : F.TopologicalData) {a b c : ℕ} (h : a = b)
    (h' : b = c) :
    letI := T.topology
    generalLinearRankCast.{uF, uV} T h ⋙ generalLinearRankCast T h' =
      generalLinearRankCast T (h.trans h') := by
  subst h h'
  exact Functor.id_comp _

theorem generalLinearRankCast_symm_comp (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    generalLinearRankCast.{uF, uV} T h ⋙ generalLinearRankCast T h.symm =
      𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)) := by
  subst h
  exact Functor.id_comp _

/-! ## Derivatives indexed by source rank and order -/

/-- The `k`-th derivative `GL_N → GL_(N-k)`: the identity for `k = 0`, and otherwise the
positive derivative `GL_((N-k)+(k-1)+1) → GL_(N-k)` after the rank transport. -/
def generalLinearDerivative (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N : ℕ) :
    (k : ℕ) → k ≤ N →
      letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier) ⥤
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N - k) F.Carrier)
  | 0, _ => letI := T.topology; 𝟭 _
  | k + 1, hk => letI := T.topology
      generalLinearRankCast T (rank_eq_of_succ_le hk) ⋙
        generalLinearDerivativePositive T ψ (N - (k + 1)) k

/-- The zeroth derivative is the identity functor. -/
theorem generalLinearDerivative_zero (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N : ℕ) (hk : 0 ≤ N) :
    letI := T.topology
    generalLinearDerivative.{uF, uV} T ψ N 0 hk =
      𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)) :=
  rfl

theorem generalLinearDerivative_succ (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N k : ℕ) (hk : k + 1 ≤ N) :
    letI := T.topology
    generalLinearDerivative.{uF, uV} T ψ N (k + 1) hk =
      generalLinearRankCast T (rank_eq_of_succ_le hk) ⋙
        generalLinearDerivativePositive T ψ (N - (k + 1)) k :=
  rfl

/-- At positive order `k`, the derivative is the positive derivative of order `k`,
`GL_((N-k)+(k-1)+1) → GL_(N-k)`, after the transport along `N = (N-k)+(k-1)+1`. -/
theorem generalLinearDerivative_of_pos (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N k : ℕ) (hk : k ≤ N)
    (hpos : 0 < k) :
    letI := T.topology
    generalLinearDerivative.{uF, uV} T ψ N k hk =
      generalLinearRankCast T (rank_eq_of_pos_le hk hpos) ⋙
        generalLinearDerivativePositive T ψ (N - k) (k - 1) := by
  cases k with
  | zero => exact absurd hpos (Nat.lt_irrefl 0)
  | succ k => rfl

theorem generalLinearDerivative_succ_obj (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N k : ℕ) (hk : k + 1 ≤ N) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier),
      (generalLinearDerivative T ψ N (k + 1) hk).obj A =
        (generalLinearDerivativePositive T ψ (N - (k + 1)) k).obj
          ((generalLinearRankCast T (rank_eq_of_succ_le hk)).obj A) := by
  intros
  rfl

/-- The top derivative of `GL_(n+1)`, with target `GL_0`, is the positive derivative
`GL_(0+n+1) → GL_0` of order `n + 1` after the transport along `n + 1 = 0 + n + 1`. -/
theorem generalLinearDerivative_top_succ (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) (hk : n + 1 ≤ n + 1) :
    letI := T.topology
    generalLinearDerivative.{uF, uV} T ψ (n + 1) (n + 1) hk ⋙
        generalLinearRankCast T (Nat.sub_self (n + 1)) =
      generalLinearRankCast T (Nat.zero_add (n + 1)).symm ⋙
        generalLinearDerivativePositive T ψ 0 n := by
  let _ := T.topology
  have key : ∀ (m : ℕ) (hm : m = 0) (h₁ : n + 1 = m + n + 1),
      generalLinearRankCast.{uF, uV} T h₁ ⋙ generalLinearDerivativePositive T ψ m n ⋙
          generalLinearRankCast T hm =
        generalLinearRankCast T (Nat.zero_add (n + 1)).symm ⋙
          generalLinearDerivativePositive T ψ 0 n := by
    intro m hm h₁
    subst hm
    exact congrArg (generalLinearRankCast T h₁ ⋙ ·) (Functor.comp_id _)
  exact key (n + 1 - (n + 1)) (Nat.sub_self (n + 1)) (rank_eq_of_succ_le hk)

end Langlands.AllFieldBZ.Derivative
