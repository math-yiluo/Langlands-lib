import Langlands.GroupScheme.Quaternionic.HyperbolicPair
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Polar duality between opposite pieces of a spanning decomposition -/

noncomputable section

universe u v w z

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]

/-- Coordinates of the polar pairing against a basis of a second subspace,
as a left `D`-linear map on the first subspace. -/
def polarPairingCoordinates (H : Matrix n n D) (U V : Submodule D (n → D))
    {ι : Type*} (b : Module.Basis ι D V) : U →ₗ[D] (ι → D) where
  toFun x j := σ.sesqForm H x (b j)
  map_add' x x' := by
    funext j
    exact σ.sesqForm_add_left _ _ _ _
  map_smul' d x := by
    funext j
    exact σ.sesqForm_smul_left _ _ _ _

/-- Pairing with a fixed row vanishes on a subspace if it vanishes on a basis.
The second variable is semilinear, so this is stated directly for its zero set. -/
theorem sesqForm_eq_zero_on_submodule_of_basis
    (H : Matrix n n D) (x : n → D) (V : Submodule D (n → D))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι D V)
    (hb : ∀ j, σ.sesqForm H x (b j) = 0) :
    ∀ y : V, σ.sesqForm H x y = 0 := by
  classical
  intro y
  have hsum (s : Finset ι) :
      σ.sesqForm H x (↑(∑ j ∈ s, b.repr y j • b j) : n → D) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj hs =>
      rw [Finset.sum_insert hj]
      change σ.sesqForm H x
        (b.repr y j • (b j : n → D) + ↑(∑ j ∈ s, b.repr y j • b j)) = 0
      rw [sesqForm_add_right, sesqForm_smul_right, hb, hs, zero_mul, add_zero]
  simpa only [b.sum_repr y] using hsum Finset.univ

variable {A : Type z}

/-- If a spanning family is orthogonal away from a designated partner, the polar
pairing restricted to those two pieces has no left radical. -/
theorem eq_zero_of_polar_pairing_partner
    (q : σ.QuadraticForms n) (hq : σ.IsNondegenerateQuadratic q)
    (W : A → Submodule D (n → D)) (hspan : (⨆ a, W a) = ⊤)
    (a b : A)
    (horth : ∀ c, c ≠ b → ∀ x ∈ W a, ∀ y ∈ W c,
      σ.sesqForm (σ.polar q) x y = 0)
    (x : W a) (hx : ∀ y : W b, σ.sesqForm (σ.polar q) x y = 0) :
    x = 0 := by
  apply Subtype.ext
  change (x : n → D) = 0
  by_contra hne
  obtain ⟨y, hy⟩ := σ.exists_polar_partner q hq x hne
  have hymem : y ∈ ⨆ c, W c := by rw [hspan]; trivial
  have hz : σ.sesqForm (σ.polar q) x y = 0 := by
    refine Submodule.iSup_induction W
      (motive := fun y => σ.sesqForm (σ.polar q) x y = 0) hymem ?_ ?_ ?_
    · intro c z hz
      by_cases hcb : c = b
      · subst c
        exact hx ⟨z, hz⟩
      · exact horth c hcb x x.2 z hz
    · exact σ.sesqForm_zero_right _ _
    · intro z z' hz hz'
      rw [sesqForm_add_right, hz, hz', add_zero]
  exact zero_ne_one (hz.symm.trans hy)

/-- Pairing with a basis of the partner gives an injective linear map, so the
dimension of a piece is bounded by that of its partner. -/
theorem finrank_le_polar_partner
    (q : σ.QuadraticForms n) (hq : σ.IsNondegenerateQuadratic q)
    (W : A → Submodule D (n → D)) (hspan : (⨆ a, W a) = ⊤)
    (a b : A)
    (horth : ∀ c, c ≠ b → ∀ x ∈ W a, ∀ y ∈ W c,
      σ.sesqForm (σ.polar q) x y = 0) :
    Module.finrank D (W a) ≤ Module.finrank D (W b) := by
  let B := Module.finBasis D (W b)
  let F := σ.polarPairingCoordinates (σ.polar q) (W a) (W b) B
  have hF : Function.Injective F := by
    apply (injective_iff_map_eq_zero F).mpr
    intro x hx
    apply σ.eq_zero_of_polar_pairing_partner q hq W hspan a b horth x
    apply σ.sesqForm_eq_zero_on_submodule_of_basis (σ.polar q) x (W b) B
    intro j
    exact congrFun hx j
  simpa using LinearMap.finrank_le_finrank_of_injective hF

/-- Opposite pieces of a spanning decomposition have the same division-algebra
dimension when the nondegenerate polar form pairs only opposite pieces. -/
theorem finrank_eq_polar_partner
    (q : σ.QuadraticForms n) (hq : σ.IsNondegenerateQuadratic q)
    (W : A → Submodule D (n → D)) (hspan : (⨆ a, W a) = ⊤)
    (τ : A → A) (hτ : Function.Involutive τ)
    (horth : ∀ a b, b ≠ τ a → ∀ x ∈ W a, ∀ y ∈ W b,
      σ.sesqForm (σ.polar q) x y = 0) (a : A) :
    Module.finrank D (W a) = Module.finrank D (W (τ a)) := by
  apply Nat.le_antisymm
  · exact σ.finrank_le_polar_partner q hq W hspan a (τ a) (horth a)
  · have hdim :=
      σ.finrank_le_polar_partner q hq W hspan (τ a) (τ (τ a)) (horth (τ a))
    rw [hτ a] at hdim
    exact hdim

/-- In a grading orthogonal away from opposite degrees, opposite degrees have
equal dimension. No independence of the graded pieces is required here. -/
theorem finrank_eq_neg_of_polar_orthogonal
    {Γ : Type z} [AddGroup Γ]
    (q : σ.QuadraticForms n) (hq : σ.IsNondegenerateQuadratic q)
    (W : Γ → Submodule D (n → D)) (hspan : (⨆ a, W a) = ⊤)
    (horth : ∀ a b, a + b ≠ 0 → ∀ x ∈ W a, ∀ y ∈ W b,
      σ.sesqForm (σ.polar q) x y = 0) (a : Γ) :
    Module.finrank D (W a) = Module.finrank D (W (-a)) := by
  apply σ.finrank_eq_polar_partner q hq W hspan (fun a => -a) neg_neg
  intro a b hab
  apply horth a b
  intro hz
  exact hab (eq_neg_of_add_eq_zero_right hz)

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
