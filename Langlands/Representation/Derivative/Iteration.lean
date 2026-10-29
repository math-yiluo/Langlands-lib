import Langlands.Representation.Derivative.MirabolicMinus

/-!
# Bernstein–Zelevinsky derivatives by iterated minus functors

The mirabolic derivative `Ψ⁻ ∘ (Φ⁻)^k` and the `GL` derivative obtained by first
restricting to the actual mirabolic subgroup, composed from the published
determinant-normalized minus functors. The ranks decrease one step at a time. A
wrapper indexed by source rank `N` and order `k ≤ N` transports the positive
derivatives along the proved rank equality. No exactness is asserted.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

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

theorem phiMinusIterate_one (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    phiMinusIterate.{uF, uV} T ψ n 1 = Mirabolic.phiMinus T ψ n :=
  Functor.comp_id _

/-- One `Φ⁻` step on objects: the largest-rank functor is applied first. -/
theorem phiMinusIterate_obj_succ (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + k + 1) F.Carrier),
      (phiMinusIterate T ψ n (k + 1)).obj A =
        (phiMinusIterate T ψ n k).obj ((Mirabolic.phiMinus T ψ (n + k)).obj A) := by
  intros
  rfl

/-- One `Φ⁻` step on morphisms. -/
theorem phiMinusIterate_map_succ (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + k + 1) F.Carrier)} (f : A ⟶ B),
      (phiMinusIterate T ψ n (k + 1)).map f =
        (phiMinusIterate T ψ n k).map ((Mirabolic.phiMinus T ψ (n + k)).map f) := by
  intros
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

theorem mirabolicDerivative_obj (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + k) F.Carrier),
      (mirabolicDerivative T ψ n k).obj A =
        (Mirabolic.psiMinus T n).obj ((phiMinusIterate T ψ n k).obj A) := by
  intros
  rfl

theorem mirabolicDerivative_map (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + k) F.Carrier)} (f : A ⟶ B),
      (mirabolicDerivative T ψ n k).map f =
        (Mirabolic.psiMinus T n).map ((phiMinusIterate T ψ n k).map f) := by
  intros
  rfl

/-! ## Restriction from `GL_(n+1)` to the mirabolic subgroup -/

/-- Restriction along the actual continuous inclusion `P_(n+1) ≤ GL_(n+1)`. -/
def generalLinearRestriction (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) := by
  letI := T.topology
  exact Mirabolic.continuousPullbackFunctor (mirabolic n F.Carrier).subtype
    continuous_subtype_val

theorem generalLinearRestriction_eq (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    generalLinearRestriction.{uF, uV} T n =
      Mirabolic.continuousPullbackFunctor (mirabolic n F.Carrier).subtype
        continuous_subtype_val :=
  rfl

/-- Restriction keeps the carrier. -/
theorem generalLinearRestriction_obj_carrier (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier),
      ((generalLinearRestriction T n).obj A : Type uV) = A := by
  intros
  rfl

/-- The restricted action is the action composed with the subgroup inclusion. -/
theorem generalLinearRestriction_obj_representation (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier),
      ((generalLinearRestriction T n).obj A).representation =
        A.representation.comp (mirabolic n F.Carrier).subtype := by
  intros
  rfl

theorem generalLinearRestriction_action (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier))
      (h : mirabolic n F.Carrier) (v : A),
      ((generalLinearRestriction T n).obj A).representation h v =
        A.representation (h : GeneralLinear (n + 1) F.Carrier) v := by
  intros
  rfl

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

/-- The fully unfolded composite `Ψ⁻ ∘ (Φ⁻)^k ∘ Res`. -/
theorem generalLinearDerivativePositive_eq_comp (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    generalLinearDerivativePositive.{uF, uV} T ψ n k =
      generalLinearRestriction T (n + k) ⋙ phiMinusIterate T ψ n k ⋙ Mirabolic.psiMinus T n :=
  rfl

/-- The first derivative is `Ψ⁻ ∘ Res`. -/
theorem generalLinearDerivativePositive_zero (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    generalLinearDerivativePositive.{uF, uV} T ψ n 0 =
      generalLinearRestriction T n ⋙ Mirabolic.psiMinus T n := by
  let _ := T.topology
  exact congrArg (generalLinearRestriction T n ⋙ ·) (mirabolicDerivative_zero T ψ n)

theorem generalLinearDerivativePositive_succ (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    generalLinearDerivativePositive.{uF, uV} T ψ n (k + 1) =
      generalLinearRestriction T (n + k + 1) ⋙ Mirabolic.phiMinus T ψ (n + k) ⋙
        mirabolicDerivative T ψ n k := by
  let _ := T.topology
  exact congrArg (generalLinearRestriction T (n + k + 1) ⋙ ·) (mirabolicDerivative_succ T ψ n k)

theorem generalLinearDerivativePositive_obj (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + k + 1) F.Carrier),
      (generalLinearDerivativePositive T ψ n k).obj A =
        (mirabolicDerivative T ψ n k).obj ((generalLinearRestriction T (n + k)).obj A) := by
  intros
  rfl

theorem generalLinearDerivativePositive_map (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + k + 1) F.Carrier)} (f : A ⟶ B),
      (generalLinearDerivativePositive T ψ n k).map f =
        (mirabolicDerivative T ψ n k).map ((generalLinearRestriction T (n + k)).map f) := by
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

/-- On objects, the rank transport is the cast along the equality of categories. -/
theorem generalLinearRankCast_obj (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier),
      (generalLinearRankCast T h).obj A =
        cast (congrArg (fun c => SmoothRep.{0, uF, uV} ℂ (GeneralLinear c F.Carrier)) h) A := by
  subst h
  intros
  rfl

/-- On morphisms, the rank transport is heterogeneously equal to the identity. -/
theorem generalLinearRankCast_map_heq (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)} (f : A ⟶ B),
      HEq ((generalLinearRankCast T h).map f) f := by
  subst h
  intros
  exact HEq.rfl

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

theorem generalLinearRankCast_comp_symm (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    generalLinearRankCast.{uF, uV} T h.symm ⋙ generalLinearRankCast T h =
      𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) := by
  subst h
  exact Functor.id_comp _

/-! ## Derivatives indexed by source rank and order -/

theorem rank_eq_of_succ_le {N k : ℕ} (hk : k + 1 ≤ N) : N = N - (k + 1) + k + 1 := by
  omega

theorem rank_eq_of_pos_le {N k : ℕ} (hk : k ≤ N) (hpos : 0 < k) :
    N = N - k + (k - 1) + 1 := by
  omega

theorem rank_eq_top_of_pos {N : ℕ} (hpos : 0 < N) : N = 0 + (N - 1) + 1 := by
  omega

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

/-- The derivative does not depend on the proof of `k ≤ N`. -/
theorem generalLinearDerivative_proof_irrel (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N k : ℕ) (hk hk' : k ≤ N) :
    letI := T.topology
    generalLinearDerivative.{uF, uV} T ψ N k hk = generalLinearDerivative T ψ N k hk' :=
  rfl

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

theorem generalLinearDerivative_succ_map (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N k : ℕ) (hk : k + 1 ≤ N) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)} (f : A ⟶ B),
      (generalLinearDerivative T ψ N (k + 1) hk).map f =
        (generalLinearDerivativePositive T ψ (N - (k + 1)) k).map
          ((generalLinearRankCast T (rank_eq_of_succ_le hk)).map f) := by
  intros
  rfl

/-- The first derivative of `GL_(n+1)` needs no rank transport: it is `Ψ⁻ ∘ Res`. -/
theorem generalLinearDerivative_one (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) (hk : 1 ≤ n + 1) :
    letI := T.topology
    generalLinearDerivative.{uF, uV} T ψ (n + 1) 1 hk =
      generalLinearRestriction T n ⋙ Mirabolic.psiMinus T n := by
  let _ := T.topology
  exact (Functor.id_comp _).trans (generalLinearDerivativePositive_zero T ψ n)

theorem generalLinearDerivative_zero_zero (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (hk : 0 ≤ 0) :
    letI := T.topology
    generalLinearDerivative.{uF, uV} T ψ 0 0 hk =
      𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier)) :=
  rfl

theorem generalLinearDerivative_one_zero (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (hk : 0 ≤ 1) :
    letI := T.topology
    generalLinearDerivative.{uF, uV} T ψ 1 0 hk =
      𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear 1 F.Carrier)) :=
  rfl

/-- The only positive derivative of `GL_1` is `Ψ⁻ ∘ Res : GL_1 → GL_0`. -/
theorem generalLinearDerivative_one_one (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (hk : 1 ≤ 1) :
    letI := T.topology
    generalLinearDerivative.{uF, uV} T ψ 1 1 hk =
      generalLinearRestriction T 0 ⋙ Mirabolic.psiMinus T 0 :=
  generalLinearDerivative_one T ψ 0 hk

/-- The top derivative of `GL_0`, with target `GL_0`, is the identity. -/
theorem generalLinearDerivative_top_zero (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (hk : 0 ≤ 0) :
    letI := T.topology
    generalLinearDerivative.{uF, uV} T ψ 0 0 hk ⋙ generalLinearRankCast T (Nat.sub_self 0) =
      𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier)) :=
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

/-- The top derivative of `GL_N` for `0 < N`, with target `GL_0`, is the positive
derivative `GL_(0+(N-1)+1) → GL_0` of order `N` after the transport along
`N = 0 + (N-1) + 1`. -/
theorem generalLinearDerivative_top (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N : ℕ) (hk : N ≤ N)
    (hpos : 0 < N) :
    letI := T.topology
    generalLinearDerivative.{uF, uV} T ψ N N hk ⋙ generalLinearRankCast T (Nat.sub_self N) =
      generalLinearRankCast T (rank_eq_top_of_pos hpos) ⋙
        generalLinearDerivativePositive T ψ 0 (N - 1) := by
  cases N with
  | zero => exact absurd hpos (Nat.lt_irrefl 0)
  | succ n => exact generalLinearDerivative_top_succ T ψ n hk

end Langlands.Derivative
