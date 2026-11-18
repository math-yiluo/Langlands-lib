import Langlands.GroupScheme.SL2CentralExtension.Setup
import Mathlib.Tactic.ComputeDegree

/-! # Lifts of matrices in one root group commute -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SL2CentralExtension

variable {S : Scheme.{u}}

namespace Ext

variable (X : Ext S)

/-! ### Lifting products -/

theorem Q_mul_res {V T : Over S} (g : V ⟶ T) {e₁ e₂ : V ⟶ X.E.X}
    {m₁ m₂ : Mat.SL2 Γ(T.left, ⊤)} (h₁ : X.Q V e₁ = res g m₁) (h₂ : X.Q V e₂ = res g m₂) :
    X.Q V (e₁ * e₂) = res g (m₁ * m₂) := by
  rw [map_mul, map_mul, h₁, h₂]

theorem Q_inv_res {V T : Over S} (g : V ⟶ T) {e : V ⟶ X.E.X}
    {m : Mat.SL2 Γ(T.left, ⊤)} (h : X.Q V e = res g m) :
    X.Q V e⁻¹ = res g m⁻¹ := by
  rw [map_inv, map_inv, h]

theorem Q_conj_res {V T : Over S} (g : V ⟶ T) {f e : V ⟶ X.E.X}
    {m n : Mat.SL2 Γ(T.left, ⊤)} (hf : X.Q V f = res g m) (he : X.Q V e = res g n) :
    X.Q V (f * e * f⁻¹) = res g (m * n * m⁻¹) := by
  simp only [map_mul, map_inv, hf, he]

/-- Lifts of commuting matrices have a central commutator. -/
theorem commutator_central_res {V T : Over S} (g : V ⟶ T) {e₁ e₂ : V ⟶ X.E.X}
    {m₁ m₂ : Mat.SL2 Γ(T.left, ⊤)} (h₁ : X.Q V e₁ = res g m₁) (h₂ : X.Q V e₂ = res g m₂)
    (h : Commute m₁ m₂) : ∀ y, Commute (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) y :=
  X.commutator_central (by rw [h₁, h₂]; exact h.map (res g))

theorem root_commute (b : Bool) {R : Type*} [CommRing R] (u₁ u₂ : R) :
    Commute (Mat.root b u₁) (Mat.root b u₂) :=
  Mat.root_comm b u₁ u₂

/-! ### The commutator pairing on one root group -/

variable (b : Bool)

/-- The commutator of local lifts of two matrices of the root group `b`. -/
def β {T : Over S} (u₁ u₂ : Γ(T.left, ⊤)) : T ⟶ X.E.X :=
  X.comm (Mat.root b u₁) (Mat.root b u₂)

theorem β_res {V T : Over S} (g : V ⟶ T) (u₁ u₂ : Γ(T.left, ⊤)) :
    g ≫ X.β b u₁ u₂ = X.β b (ring g u₁) (ring g u₂) := by
  simp only [β]
  rw [comm_res, Mat.map_root, Mat.map_root]

theorem Q_β {T : Over S} (u₁ u₂ : Γ(T.left, ⊤)) : X.Q T (X.β b u₁ u₂) = 1 := by
  rw [β, Q_comm, Mat.root_comm b u₁ u₂, mul_inv_cancel_right, mul_inv_cancel]

theorem β_central {T : Over S} (u₁ u₂ : Γ(T.left, ⊤)) (y : T ⟶ X.E.X) :
    Commute (X.β b u₁ u₂) y :=
  X.central _ y (X.Q_β b u₁ u₂)

theorem β_add_right {T : Over S} (u v v' : Γ(T.left, ⊤)) :
    X.β b u (v + v') = X.β b u v * X.β b u v' := by
  apply Loc.ext
  refine (((X.lift (Mat.root b u)).and (X.lift (Mat.root b v))).and
    (X.lift (Mat.root b v'))).mono ?_
  rintro V g ⟨⟨⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩, ⟨e₃, h₃⟩⟩
  have h23 : X.Q V (e₂ * e₃) = res g (Mat.root b (v + v')) := by
    rw [Mat.root_add]; exact X.Q_mul_res g h₂ h₃
  rw [MonObj.comp_mul]
  simp only [β]
  rw [X.comm_spec _ _ g e₁ _ h₁ h23, X.comm_spec _ _ g e₁ e₂ h₁ h₂,
    X.comm_spec _ _ g e₁ e₃ h₁ h₃]
  exact commutator_mul_right e₁ e₂ e₃
    (X.commutator_central_res g h₁ h₃ (root_commute b u v'))

theorem β_add_left {T : Over S} (u u' v : Γ(T.left, ⊤)) :
    X.β b (u + u') v = X.β b u v * X.β b u' v := by
  apply Loc.ext
  refine (((X.lift (Mat.root b u)).and (X.lift (Mat.root b u'))).and
    (X.lift (Mat.root b v))).mono ?_
  rintro V g ⟨⟨⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩, ⟨e₃, h₃⟩⟩
  have h12 : X.Q V (e₁ * e₂) = res g (Mat.root b (u + u')) := by
    rw [Mat.root_add]; exact X.Q_mul_res g h₁ h₂
  rw [MonObj.comp_mul]
  simp only [β]
  rw [X.comm_spec _ _ g _ e₃ h12 h₃, X.comm_spec _ _ g e₁ e₃ h₁ h₃,
    X.comm_spec _ _ g e₂ e₃ h₂ h₃]
  exact commutator_mul_left e₁ e₂ e₃
    (X.commutator_central_res g h₂ h₃ (root_commute b u' v))

/-- Conjugating by a lift of `λ_b(s)` scales both arguments by `s²`. -/
theorem β_conj {T : Over S} (s : Γ(T.left, ⊤)ˣ) (u₁ u₂ : Γ(T.left, ⊤)) :
    X.β b ((s : Γ(T.left, ⊤)) * (s : Γ(T.left, ⊤)) * u₁)
      ((s : Γ(T.left, ⊤)) * (s : Γ(T.left, ⊤)) * u₂) = X.β b u₁ u₂ := by
  apply Loc.ext
  refine (((X.lift (Mat.lam b s)).and (X.lift (Mat.root b u₁))).and
    (X.lift (Mat.root b u₂))).mono ?_
  rintro V g ⟨⟨⟨f, hf⟩, ⟨e₁, h₁⟩⟩, ⟨e₂, h₂⟩⟩
  have k₁ : X.Q V (f * e₁ * f⁻¹) =
      res g (Mat.root b ((s : Γ(T.left, ⊤)) * (s : Γ(T.left, ⊤)) * u₁)) := by
    rw [← Mat.lam_root_conj]; exact X.Q_conj_res g hf h₁
  have k₂ : X.Q V (f * e₂ * f⁻¹) =
      res g (Mat.root b ((s : Γ(T.left, ⊤)) * (s : Γ(T.left, ⊤)) * u₂)) := by
    rw [← Mat.lam_root_conj]; exact X.Q_conj_res g hf h₂
  simp only [β]
  rw [X.comm_spec _ _ g _ _ k₁ k₂, X.comm_spec _ _ g e₁ e₂ h₁ h₂, ← conj_commutator,
    ← (X.commutator_central_res g h₁ h₂ (root_commute b u₁ u₂) f).eq, mul_inv_cancel_right]

/-- Scaling both arguments by a unit does not change the pairing (fppf-locally the unit is a
square). -/
theorem β_unit {T : Over S} (s : Γ(T.left, ⊤)ˣ) (u₁ u₂ : Γ(T.left, ⊤)) :
    X.β b ((s : Γ(T.left, ⊤)) * u₁) ((s : Γ(T.left, ⊤)) * u₂) = X.β b u₁ u₂ := by
  rcases subsingleton_or_nontrivial Γ(T.left, ⊤) with hT | hT
  · rw [Subsingleton.elim ((s : Γ(T.left, ⊤)) * u₁) u₁,
      Subsingleton.elim ((s : Γ(T.left, ⊤)) * u₂) u₂]
  apply Loc.ext
  have hp : (Polynomial.X ^ 2 - Polynomial.C (s : Γ(T.left, ⊤))).Monic :=
    Polynomial.monic_X_pow_sub_C _ two_ne_zero
  have hdeg : 0 < (Polynomial.X ^ 2 - Polynomial.C (s : Γ(T.left, ⊤))).natDegree := by
    rw [Polynomial.natDegree_X_pow_sub_C]; norm_num
  refine (Loc.exists_root _ hp hdeg).mono ?_
  rintro V g ⟨r, hr⟩
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hr
  have hrs : r * r = ring g s := by rw [← sq]; exact sub_eq_zero.mp hr
  have hrr : IsUnit (r * r) := by rw [hrs]; exact s.isUnit.map (ring g)
  have hru : IsUnit r := isUnit_of_mul_isUnit_left hrr
  rw [β_res, β_res, map_mul, map_mul, ← hrs]
  have := X.β_conj b hru.unit (ring g u₁) (ring g u₂)
  simpa only [IsUnit.unit_spec] using this

/-- If `r`, `1 + r` and `r² + r + 1` are units, the pairing vanishes. -/
theorem β_eq_one_of_units {T : Over S} (r : Γ(T.left, ⊤)) (hr : IsUnit r) (hr₁ : IsUnit (1 + r))
    (hr₂ : IsUnit (r * r + r + 1)) (u v : Γ(T.left, ⊤)) : X.β b u v = 1 := by
  have hsc : ∀ u v, X.β b (r * u) (r * v) = X.β b u v := by
    intro u v
    have := X.β_unit b hr.unit u v
    rwa [IsUnit.unit_spec] at this
  have key : ∀ v, X.β b u (r * v) * X.β b (r * u) v * X.β b u v = 1 := by
    intro v
    have h1 := X.β_unit b hr₁.unit u v
    rw [IsUnit.unit_spec, add_mul, add_mul, one_mul, one_mul, X.β_add_left, X.β_add_right,
      X.β_add_right, hsc u v] at h1
    refine mul_left_cancel (a := X.β b u v) ?_
    rw [mul_one]
    convert h1 using 1
    simp only [mul_assoc]
  have key2 : ∀ w, X.β b u ((r * r + r + 1) * w) = 1 := by
    intro w
    have e1 := key (r * w)
    rw [hsc u w] at e1
    have : (r * r + r + 1) * w = r * (r * w) + w + r * w := by ring
    rw [this, X.β_add_right, X.β_add_right]
    exact e1
  rw [show v = (r * r + r + 1) * (↑hr₂.unit⁻¹ * v) by
    rw [← mul_assoc, hr₂.mul_val_inv, one_mul]]
  exact key2 _

/-- The commutator pairing on a root group is trivial. -/
theorem β_eq_one {T : Over S} (u₁ u₂ : Γ(T.left, ⊤)) : X.β b u₁ u₂ = 1 := by
  let p : Polynomial Γ(T.left, ⊤) := Polynomial.X * (Polynomial.X + 1) *
    (Polynomial.X * Polynomial.X + Polynomial.X + 1)
  have hp : Nondeg p := Nondeg.monic (by simp only [p]; monicity!)
  apply Loc.ext
  refine (Loc.exists_isUnit_eval p hp).mono ?_
  rintro V g ⟨r, hr⟩
  simp only [p, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X, Polynomial.map_one,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] at hr
  rw [IsUnit.mul_iff, IsUnit.mul_iff] at hr
  obtain ⟨⟨h0, h1⟩, h2⟩ := hr
  rw [β_res, MonObj.comp_one]
  exact X.β_eq_one_of_units b r h0 (by rw [add_comm]; exact h1) h2 _ _

/-- Lifts of two matrices of the same root group commute. -/
theorem commute_of_root {T : Over S} {e₁ e₂ : T ⟶ X.E.X} {u₁ u₂ : Γ(T.left, ⊤)}
    (h₁ : X.Q T e₁ = Mat.root b u₁) (h₂ : X.Q T e₂ = Mat.root b u₂) : Commute e₁ e₂ := by
  have := X.comm_eq h₁ h₂
  change X.β b u₁ u₂ = _ at this
  rw [β_eq_one] at this
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp this.symm)

end Ext

end Langlands.GroupScheme.SL2CentralExtension
