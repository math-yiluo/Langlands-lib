import Langlands.GroupScheme.SpecialLinearTernaryLift

/-! # The ternary relations from weak root group relations -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open Matrix

namespace Langlands.GroupScheme.SpecialLinear.TernaryPresentation

/-- Binary special linear group. -/
local notation "SL2" A => Matrix.SpecialLinearGroup (Fin 2) A

open BinaryPresentation Matrix.SpecialLinearGroup

variable {F : Type u} [Field F] {H : Type v} [Group H]

section WeylElement

/-- `x(s) y(-s⁻¹) x(s) = h(s) w⁻¹` in binary `SL`. -/
theorem upper_mul_lower_mul_upper {s : F} (hs : s ≠ 0) :
    upper s * lower (-s⁻¹) * upper s =
      BinaryPresentation.diag (Units.mk0 s hs) * (BinaryUpper.weylMatrix)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  ext i j
  rw [coe_mul, coe_mul, coe_mul, coe_upper, coe_lower, coe_diag, coe_weylMatrix]
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, hs]

theorem upper_neg (s : F) : (upper (-s) : SL2 F) = (upper s)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← upper_add, neg_add_cancel, upper_zero]

theorem diag_neg_one_inv : (BinaryPresentation.diag (-1 : Fˣ) : SL2 F)⁻¹ =
    BinaryPresentation.diag (-1) := by
  rw [← binaryDiag_inv]
  congr 1

variable (φ : (SL2 F) →* H)

theorem map_weyl_mul_weyl :
    φ BinaryUpper.weylMatrix * φ BinaryUpper.weylMatrix = φ (BinaryPresentation.diag (-1)) := by
  rw [← map_mul, weylMatrix_mul_weylMatrix]

theorem map_diag_neg_one_inv :
    (φ (BinaryPresentation.diag (-1)))⁻¹ = φ (BinaryPresentation.diag (-1)) := by
  rw [← map_inv, diag_neg_one_inv]

theorem map_lower_eq (r : F) :
    φ (lower r) = (φ BinaryUpper.weylMatrix)⁻¹ * φ (upper (-r)) * φ BinaryUpper.weylMatrix := by
  rw [← map_inv, ← map_mul, ← map_mul, weylMatrix_inv_conj_upper]

theorem map_upper_eq (s : F) :
    φ (upper s) = φ BinaryUpper.weylMatrix * φ (lower (-s)) * (φ BinaryUpper.weylMatrix)⁻¹ := by
  have h := weylMatrix_mul_lower (F := F) (-s)
  rw [neg_neg] at h
  rw [← map_inv, ← map_mul, ← map_mul, h, mul_inv_cancel_right]

theorem map_diag_mul_weyl (u : Fˣ) :
    φ (BinaryPresentation.diag u) * φ BinaryUpper.weylMatrix =
      φ BinaryUpper.weylMatrix * φ (BinaryPresentation.diag u⁻¹) := by
  rw [← map_mul, ← map_mul, diag_mul_weylMatrix]

/-- Conjugation by `φ(w)⁻¹` is conjugation by `φ(w)` after conjugation by `φ(diag(-1))`. -/
theorem weyl_inv_conj (g : H) :
    (φ BinaryUpper.weylMatrix)⁻¹ * g * φ BinaryUpper.weylMatrix =
      φ BinaryUpper.weylMatrix * (φ (BinaryPresentation.diag (-1)) * g *
        (φ (BinaryPresentation.diag (-1)))⁻¹) * (φ BinaryUpper.weylMatrix)⁻¹ := by
  have h : (φ (BinaryPresentation.diag (-1)))⁻¹ * g * φ (BinaryPresentation.diag (-1)) =
      φ (BinaryPresentation.diag (-1)) * g * (φ (BinaryPresentation.diag (-1)))⁻¹ := by
    nth_rewrite 1 [map_diag_neg_one_inv]
    nth_rewrite 2 [← map_diag_neg_one_inv]
    rfl
  rw [← h, ← map_weyl_mul_weyl]
  group

end WeylElement

section Corner

variable (φ ψ : (SL2 F) →* H)

theorem cornerPoint_neg (t : F) : cornerPoint φ ψ (-t) = (cornerPoint φ ψ t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← cornerPoint_add, neg_add_cancel, cornerPoint_zero]

theorem weyl_inv_conj_cornerPoint (t : F) :
    (φ BinaryUpper.weylMatrix)⁻¹ * cornerPoint φ ψ t * φ BinaryUpper.weylMatrix =
      ψ (upper (-t)) := by
  rw [cornerPoint]
  group

variable {φ ψ}
variable (ht : ∀ (u : Fˣ) (t : F), φ (BinaryPresentation.diag u) * ψ (upper t) *
    (φ (BinaryPresentation.diag u))⁻¹ = ψ (upper ((u : F)⁻¹ * t)))
include ht

theorem weyl_conj_cornerPoint (t : F) :
    φ BinaryUpper.weylMatrix * cornerPoint φ ψ t * (φ BinaryUpper.weylMatrix)⁻¹ =
      ψ (upper t) := by
  have h := ht (-1) (-t)
  rw [show ((-1 : Fˣ) : F)⁻¹ * -t = t by simp, ← map_weyl_mul_weyl] at h
  rw [← h, cornerPoint]
  group

theorem weyl_inv_conj_upper (c : F) :
    (φ BinaryUpper.weylMatrix)⁻¹ * ψ (upper c) * φ BinaryUpper.weylMatrix = cornerPoint φ ψ c := by
  rw [weyl_inv_conj, ht, cornerPoint]
  congr 3
  simp

theorem torus_conj_cornerPoint_of (u : Fˣ) (t : F) :
    φ (BinaryPresentation.diag u) * cornerPoint φ ψ t * (φ (BinaryPresentation.diag u))⁻¹ =
      cornerPoint φ ψ ((u : F) * t) := by
  have hw := map_diag_mul_weyl φ u
  have h := ht u⁻¹ (-t)
  rw [Units.val_inv_eq_inv_val, inv_inv] at h
  calc φ (BinaryPresentation.diag u) * cornerPoint φ ψ t * (φ (BinaryPresentation.diag u))⁻¹
      = (φ (BinaryPresentation.diag u) * φ BinaryUpper.weylMatrix) * ψ (upper (-t)) *
          (φ (BinaryPresentation.diag u) * φ BinaryUpper.weylMatrix)⁻¹ := by
        simp only [cornerPoint]; group
    _ = φ BinaryUpper.weylMatrix * (φ (BinaryPresentation.diag u⁻¹) * ψ (upper (-t)) *
          (φ (BinaryPresentation.diag u⁻¹))⁻¹) * (φ BinaryUpper.weylMatrix)⁻¹ := by
        rw [hw]; group
    _ = cornerPoint φ ψ ((u : F) * t) := by rw [h, cornerPoint, mul_neg]

omit ht in
theorem commute_upper_cornerPoint_of (hy : ∀ r c : F, Commute (φ (lower r)) (ψ (upper c)))
    (s t : F) : Commute (φ (upper s)) (cornerPoint φ ψ t) := by
  rw [map_upper_eq φ s, cornerPoint]
  have h := (hy (-s) (-t)).eq
  change _ * _ = _ * _
  calc φ BinaryUpper.weylMatrix * φ (lower (-s)) * (φ BinaryUpper.weylMatrix)⁻¹ *
        (φ BinaryUpper.weylMatrix * ψ (upper (-t)) * (φ BinaryUpper.weylMatrix)⁻¹)
      = φ BinaryUpper.weylMatrix * (φ (lower (-s)) * ψ (upper (-t))) *
          (φ BinaryUpper.weylMatrix)⁻¹ := by group
    _ = φ BinaryUpper.weylMatrix * (ψ (upper (-t)) * φ (lower (-s))) *
          (φ BinaryUpper.weylMatrix)⁻¹ := by rw [h]
    _ = _ := by group

/-- **Exact commutator from weak relations.** Let `φ ψ : SL₂(F) →* H`, write
`x(s) = φ(upper s)`, `y(r) = φ(lower r)`, `p(c) = ψ(upper c)` and
`q = cornerPoint φ ψ`. Suppose the torus of `φ` scales `p` by the inverse unit, `y`
commutes with `p`, `p` commutes with `q`, every `x(s) p(c) x(s)⁻¹` is `p(c) q(f)` for some
`f`, and `p(e) = q(d)` forces `p(e) = 1`. Then `x(s) p(c) x(s)⁻¹ = p(c) q(s c)`. -/
theorem conj_upper_eq_of_weak (hy : ∀ r c : F, Commute (φ (lower r)) (ψ (upper c)))
    (hpq : ∀ c d : F, Commute (ψ (upper c)) (cornerPoint φ ψ d))
    (hweak : ∀ s c : F, ∃ f : F, φ (upper s) * ψ (upper c) * (φ (upper s))⁻¹ =
      ψ (upper c) * cornerPoint φ ψ f)
    (hsep : ∀ e d : F, ψ (upper e) = cornerPoint φ ψ d → ψ (upper e) = 1) (s c : F) :
    φ (upper s) * ψ (upper c) * (φ (upper s))⁻¹ = ψ (upper c) * cornerPoint φ ψ (s * c) := by
  by_cases hs : s = 0
  · subst hs
    rw [upper_zero, map_one, one_mul, inv_one, mul_one, zero_mul, cornerPoint_zero, mul_one]
  set ν := φ BinaryUpper.weylMatrix with hν
  set w := φ (upper s) * φ (lower (-s⁻¹)) * φ (upper s) with hwdef
  have hw : w = φ (BinaryPresentation.diag (Units.mk0 s hs)) * ν⁻¹ := by
    rw [hwdef, hν, ← map_mul, ← map_mul, ← map_inv, ← map_mul, upper_mul_lower_mul_upper hs]
  -- the exact value of the conjugate by `w`
  have hex : w * ψ (upper c) * w⁻¹ = cornerPoint φ ψ (s * c) := by
    rw [hw]
    calc φ (BinaryPresentation.diag (Units.mk0 s hs)) * ν⁻¹ * ψ (upper c) *
          (φ (BinaryPresentation.diag (Units.mk0 s hs)) * ν⁻¹)⁻¹
        = φ (BinaryPresentation.diag (Units.mk0 s hs)) * (ν⁻¹ * ψ (upper c) * ν) *
            (φ (BinaryPresentation.diag (Units.mk0 s hs)))⁻¹ := by group
      _ = cornerPoint φ ψ (s * c) := by
          rw [hν, weyl_inv_conj_upper ht, torus_conj_cornerPoint_of ht, Units.val_mk0]
  -- the stepwise value
  obtain ⟨f₁, h₁⟩ := hweak s c
  obtain ⟨f₂, h₂⟩ := hweak s⁻¹ f₁
  obtain ⟨f₃, h₃⟩ := hweak s (c + -f₂)
  have hyq : φ (lower (-s⁻¹)) * cornerPoint φ ψ f₁ * (φ (lower (-s⁻¹)))⁻¹ =
      cornerPoint φ ψ f₁ * ψ (upper (-f₂)) := by
    rw [map_lower_eq φ, neg_neg]
    have e1 : ν * cornerPoint φ ψ f₁ * ν⁻¹ = ψ (upper f₁) := weyl_conj_cornerPoint ht f₁
    calc ν⁻¹ * φ (upper s⁻¹) * ν * cornerPoint φ ψ f₁ * (ν⁻¹ * φ (upper s⁻¹) * ν)⁻¹
        = ν⁻¹ * (φ (upper s⁻¹) * (ν * cornerPoint φ ψ f₁ * ν⁻¹) * (φ (upper s⁻¹))⁻¹) * ν := by
          group
      _ = (ν⁻¹ * ψ (upper f₁) * ν) * (ν⁻¹ * cornerPoint φ ψ f₂ * ν) := by
          rw [e1, h₂]; group
      _ = cornerPoint φ ψ f₁ * ψ (upper (-f₂)) := by
          rw [hν, weyl_inv_conj_upper ht, weyl_inv_conj_cornerPoint]
  have hyp : φ (lower (-s⁻¹)) * ψ (upper c) * (φ (lower (-s⁻¹)))⁻¹ = ψ (upper c) := by
    rw [(hy _ c).eq, mul_inv_cancel_right]
  have hxq : φ (upper s) * cornerPoint φ ψ f₁ * (φ (upper s))⁻¹ = cornerPoint φ ψ f₁ := by
    rw [(commute_upper_cornerPoint_of hy s f₁).eq, mul_inv_cancel_right]
  have hst : w * ψ (upper c) * w⁻¹ =
      ψ (upper (c + -f₂)) * cornerPoint φ ψ f₃ * cornerPoint φ ψ f₁ := by
    calc w * ψ (upper c) * w⁻¹
        = φ (upper s) * (φ (lower (-s⁻¹)) * (φ (upper s) * ψ (upper c) * (φ (upper s))⁻¹) *
            (φ (lower (-s⁻¹)))⁻¹) * (φ (upper s))⁻¹ := by rw [hwdef]; group
      _ = φ (upper s) * ((φ (lower (-s⁻¹)) * ψ (upper c) * (φ (lower (-s⁻¹)))⁻¹) *
            (φ (lower (-s⁻¹)) * cornerPoint φ ψ f₁ * (φ (lower (-s⁻¹)))⁻¹)) *
            (φ (upper s))⁻¹ := by rw [h₁]; group
      _ = φ (upper s) * (ψ (upper c) * (cornerPoint φ ψ f₁ * ψ (upper (-f₂)))) *
            (φ (upper s))⁻¹ := by rw [hyp, hyq]
      _ = φ (upper s) * (ψ (upper c) * ψ (upper (-f₂)) * cornerPoint φ ψ f₁) *
            (φ (upper s))⁻¹ := by rw [← (hpq (-f₂) f₁).eq]; group
      _ = (φ (upper s) * ψ (upper (c + -f₂)) * (φ (upper s))⁻¹) *
            (φ (upper s) * cornerPoint φ ψ f₁ * (φ (upper s))⁻¹) := by
          rw [upper_add, map_mul]; group
      _ = _ := by rw [h₃, hxq]
  rw [hex] at hst
  have hp : ψ (upper (c + -f₂)) = cornerPoint φ ψ (s * c + -f₁ + -f₃) := by
    rw [cornerPoint_add, cornerPoint_add, cornerPoint_neg, cornerPoint_neg, hst]
    group
  have hp1 := hsep _ _ hp
  have hq3 : cornerPoint φ ψ f₃ = 1 := by
    have h := h₃
    rw [hp1, mul_one, mul_inv_cancel, one_mul] at h
    exact h.symm
  rw [hp1, hq3, one_mul, one_mul] at hst
  rw [h₁, hst]

end Corner

section Weak

/-- Weak relations between two homomorphisms `φ₁ φ₂ : SL₂(F) →* H`: torus and Weyl
conjugation relations, commutations, the commutators of the upper root groups only up to an
unspecified point of the third root group, and separation of root groups. Write
`x₃ = cornerPoint φ₁ φ₂` and `x₃' = cornerPoint φ₂ φ₁`. -/
structure WeakTernaryRelations (φ₁ φ₂ : (SL2 F) →* H) : Prop where
  torus_upper : ∀ (u : Fˣ) (t : F), φ₁ (BinaryPresentation.diag u) * φ₂ (upper t) *
    (φ₁ (BinaryPresentation.diag u))⁻¹ = φ₂ (upper ((u : F)⁻¹ * t))
  torus_lower : ∀ (u : Fˣ) (t : F), φ₁ (BinaryPresentation.diag u) * φ₂ (lower t) *
    (φ₁ (BinaryPresentation.diag u))⁻¹ = φ₂ (lower ((u : F) * t))
  torus_upper' : ∀ (u : Fˣ) (t : F), φ₂ (BinaryPresentation.diag u) * φ₁ (upper t) *
    (φ₂ (BinaryPresentation.diag u))⁻¹ = φ₁ (upper ((u : F)⁻¹ * t))
  weyl_torus : ∀ u : Fˣ, φ₁ BinaryUpper.weylMatrix * φ₂ (BinaryPresentation.diag u) *
    (φ₁ BinaryUpper.weylMatrix)⁻¹ = φ₁ (BinaryPresentation.diag u) * φ₂ (BinaryPresentation.diag u)
  commute_lower_upper : ∀ r c : F, Commute (φ₂ (lower r)) (φ₁ (upper c))
  commute_lower_upper' : ∀ r c : F, Commute (φ₁ (lower r)) (φ₂ (upper c))
  commute_upper_corner : ∀ c t : F, Commute (φ₂ (upper c)) (cornerPoint φ₁ φ₂ t)
  commute_upper_corner' : ∀ c t : F, Commute (φ₁ (upper c)) (cornerPoint φ₂ φ₁ t)
  commute_corner : ∀ s t : F, Commute (φ₁ (upper s)) (cornerPoint φ₁ φ₂ t)
  weak_commutator : ∀ s c : F, ∃ f : F, φ₁ (upper s) * φ₂ (upper c) * (φ₁ (upper s))⁻¹ =
    φ₂ (upper c) * cornerPoint φ₁ φ₂ f
  weak_commutator' : ∀ s c : F, ∃ f : F, φ₂ (upper s) * φ₁ (upper c) * (φ₂ (upper s))⁻¹ =
    φ₁ (upper c) * cornerPoint φ₂ φ₁ f
  separation : ∀ e d : F, φ₂ (upper e) = cornerPoint φ₁ φ₂ d → φ₂ (upper e) = 1
  separation' : ∀ e d : F, φ₁ (upper e) = cornerPoint φ₂ φ₁ d → φ₁ (upper e) = 1

namespace WeakTernaryRelations

variable {φ₁ φ₂ : (SL2 F) →* H} (R : WeakTernaryRelations φ₁ φ₂)
include R

/-- The exact commutator `x₁(s) x₂(c) x₁(s)⁻¹ = x₂(c) x₃(s c)`. -/
theorem conj_upper (s c : F) :
    φ₁ (upper s) * φ₂ (upper c) * (φ₁ (upper s))⁻¹ = φ₂ (upper c) * cornerPoint φ₁ φ₂ (s * c) :=
  conj_upper_eq_of_weak R.torus_upper R.commute_lower_upper' R.commute_upper_corner
    R.weak_commutator R.separation s c

/-- The exact commutator `x₂(s) x₁(c) x₂(s)⁻¹ = x₁(c) x₃'(s c)`. -/
theorem conj_upper' (s c : F) :
    φ₂ (upper s) * φ₁ (upper c) * (φ₂ (upper s))⁻¹ = φ₁ (upper c) * cornerPoint φ₂ φ₁ (s * c) :=
  conj_upper_eq_of_weak R.torus_upper' R.commute_lower_upper R.commute_upper_corner'
    R.weak_commutator' R.separation' s c

theorem commutator (c s : F) :
    φ₂ (upper c) * φ₁ (upper s) * (φ₂ (upper c))⁻¹ = φ₁ (upper s) * cornerPoint φ₁ φ₂ (-(c * s)) := by
  have h := R.conj_upper (-s) c
  rw [upper_neg, map_inv, inv_inv] at h
  have h' : φ₂ (upper c) * φ₁ (upper s) =
      φ₁ (upper s) * (φ₂ (upper c) * cornerPoint φ₁ φ₂ (-s * c)) := by
    rw [← h]; group
  rw [h', (R.commute_upper_corner c (-s * c)).eq, show -s * c = -(c * s) by ring]
  group

/-- The second Weyl element conjugates `x₁` to `x₃`. -/
theorem weyl_conj_upper' (t : F) :
    φ₂ BinaryUpper.weylMatrix * φ₁ (upper t) * (φ₂ BinaryUpper.weylMatrix)⁻¹ =
      cornerPoint φ₁ φ₂ t := by
  have h1 := R.conj_upper' (-t) 1
  have h2 := R.commutator (-t) 1
  rw [h1, mul_right_inj] at h2
  simp only [mul_one, neg_neg] at h2
  rw [← h2, cornerPoint, neg_neg]

theorem lower_corner (c t : F) :
    φ₂ (lower c) * cornerPoint φ₁ φ₂ t * (φ₂ (lower c))⁻¹ =
      cornerPoint φ₁ φ₂ t * φ₁ (upper (-(c * t))) := by
  set ν := φ₂ BinaryUpper.weylMatrix with hν
  have e1 : ν * ν * φ₁ (upper t) * (ν * ν)⁻¹ = φ₁ (upper (-t)) := by
    rw [hν, map_weyl_mul_weyl, R.torus_upper', show ((-1 : Fˣ) : F)⁻¹ * t = -t by simp]
  have e2 : ν⁻¹ * φ₁ (upper (-t)) * ν = cornerPoint φ₁ φ₂ t := by
    rw [hν, weyl_inv_conj, R.torus_upper', ← R.weyl_conj_upper' t,
      show ((-1 : Fˣ) : F)⁻¹ * -t = t by simp]
  have e3 : ν⁻¹ * cornerPoint φ₁ φ₂ (-(c * t)) * ν = φ₁ (upper (-(c * t))) := by
    rw [← R.weyl_conj_upper', hν]
    group
  have hc := R.commutator (-c) (-t)
  rw [show -(-c * -t) = -(c * t) by ring] at hc
  rw [map_lower_eq φ₂ c, ← R.weyl_conj_upper' t]
  calc ν⁻¹ * φ₂ (upper (-c)) * ν * (ν * φ₁ (upper t) * ν⁻¹) * (ν⁻¹ * φ₂ (upper (-c)) * ν)⁻¹
      = ν⁻¹ * (φ₂ (upper (-c)) * (ν * ν * φ₁ (upper t) * (ν * ν)⁻¹) *
          (φ₂ (upper (-c)))⁻¹) * ν := by group
    _ = (ν⁻¹ * φ₁ (upper (-t)) * ν) * (ν⁻¹ * cornerPoint φ₁ φ₂ (-(c * t)) * ν) := by
        rw [e1, hc]; group
    _ = _ := by rw [e2, e3, R.weyl_conj_upper']

/-- The product `ν₁ ν₂` of the two Weyl elements conjugates `x₁(t)` to `x₂(t)`. -/
theorem weyl_mul_weyl_conj_upper (t : F) :
    (φ₁ BinaryUpper.weylMatrix * φ₂ BinaryUpper.weylMatrix) * φ₁ (upper t) *
      (φ₁ BinaryUpper.weylMatrix * φ₂ BinaryUpper.weylMatrix)⁻¹ = φ₂ (upper t) :=
  calc φ₁ BinaryUpper.weylMatrix * φ₂ BinaryUpper.weylMatrix * φ₁ (upper t) *
        (φ₁ BinaryUpper.weylMatrix * φ₂ BinaryUpper.weylMatrix)⁻¹
      = φ₁ BinaryUpper.weylMatrix * (φ₂ BinaryUpper.weylMatrix * φ₁ (upper t) *
          (φ₂ BinaryUpper.weylMatrix)⁻¹) * (φ₁ BinaryUpper.weylMatrix)⁻¹ := by group
    _ = φ₁ BinaryUpper.weylMatrix * cornerPoint φ₁ φ₂ t * (φ₁ BinaryUpper.weylMatrix)⁻¹ := by
        rw [R.weyl_conj_upper']
    _ = φ₂ (upper t) := weyl_conj_cornerPoint R.torus_upper t

variable (hlower : ∀ t : F, (φ₁ BinaryUpper.weylMatrix * φ₂ BinaryUpper.weylMatrix) *
    φ₁ (lower t) * (φ₁ BinaryUpper.weylMatrix * φ₂ BinaryUpper.weylMatrix)⁻¹ = φ₂ (lower t))
include hlower

/-- The braid relation `ν₁ ν₂ ν₁ = ν₂ ν₁ ν₂`, given that `ν₁ ν₂` also conjugates `y₁(t)` to
`y₂(t)`. -/
theorem braid :
    φ₁ BinaryUpper.weylMatrix * φ₂ BinaryUpper.weylMatrix * φ₁ BinaryUpper.weylMatrix =
      φ₂ BinaryUpper.weylMatrix * φ₁ BinaryUpper.weylMatrix * φ₂ BinaryUpper.weylMatrix := by
  have key : (MulAut.conj (φ₁ BinaryUpper.weylMatrix * φ₂ BinaryUpper.weylMatrix)).toMonoidHom.comp
      φ₁ = φ₂ := by
    apply BinaryPresentation.hom_ext
    · intro t
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact R.weyl_mul_weyl_conj_upper t
    · intro t
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hlower t
  have h := DFunLike.congr_fun key BinaryUpper.weylMatrix
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  calc φ₁ BinaryUpper.weylMatrix * φ₂ BinaryUpper.weylMatrix * φ₁ BinaryUpper.weylMatrix
      = (φ₁ BinaryUpper.weylMatrix * φ₂ BinaryUpper.weylMatrix * φ₁ BinaryUpper.weylMatrix *
          (φ₁ BinaryUpper.weylMatrix * φ₂ BinaryUpper.weylMatrix)⁻¹) *
          (φ₁ BinaryUpper.weylMatrix * φ₂ BinaryUpper.weylMatrix) := by group
    _ = φ₂ BinaryUpper.weylMatrix * (φ₁ BinaryUpper.weylMatrix * φ₂ BinaryUpper.weylMatrix) := by
        rw [h]
    _ = _ := by group

/-- **Weak relations give the ternary relations**, given that `φ₁(w) φ₂(w)` conjugates the
lower root group of `φ₁` to that of `φ₂`. -/
theorem ternaryRelations : TernaryRelations φ₁ φ₂ where
  torus_upper := R.torus_upper
  torus_lower := R.torus_lower
  weyl_torus := R.weyl_torus
  commutator := R.commutator
  commute_upper_corner := R.commute_upper_corner
  commute_lower_upper := R.commute_lower_upper
  lower_corner := R.lower_corner
  commute_corner := R.commute_corner
  braid := R.braid hlower

/-- Two homomorphisms satisfying the weak relations, such that `φ₁(w) φ₂(w)` conjugates the
lower root group of `φ₁` to that of `φ₂`, are the restrictions of one homomorphism out of
`SL₃(F)` to the two block embeddings. -/
theorem exists_lift : ∃ Φ : Matrix.SpecialLinearGroup (Fin 3) F →* H,
    Φ.comp left = φ₁ ∧ Φ.comp right = φ₂ :=
  (R.ternaryRelations hlower).exists_lift

end WeakTernaryRelations

end Weak

end Langlands.GroupScheme.SpecialLinear.TernaryPresentation
