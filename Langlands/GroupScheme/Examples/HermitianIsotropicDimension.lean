import Langlands.GroupScheme.Examples.HermitianHyperbolicReduction

/-! # Isotropic dimensions under Hermitian hyperbolic splitting -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {V : Type v} [AddCommGroup V] [Module L V]
  (h : V →ₗ[L] V →ₛₗ[(fieldInvolution K L).bar.toRingHom] L)
  (hbar : ∀ x y, (fieldInvolution K L).bar (h x y) = h y x)

/-- The actual restriction of the pairing to a hyperbolic middle. -/
def hyperbolicMiddlePairing (x y : V) :
    hyperbolicMiddle h x y →ₗ[L]
      hyperbolicMiddle h x y →ₛₗ[(fieldInvolution K L).bar.toRingHom] L :=
  h.domRestrict₁₂ (hyperbolicMiddle h x y) (hyperbolicMiddle h x y)

@[simp] theorem hyperbolicMiddlePairing_apply (x y : V)
    (z w : hyperbolicMiddle h x y) :
    hyperbolicMiddlePairing h x y z w = h (z : V) (w : V) := rfl

include hbar in
/-- The actual restricted pairing retains Hermitian symmetry. -/
theorem hyperbolicMiddlePairing_bar (x y : V)
    (z w : hyperbolicMiddle h x y) :
    (fieldInvolution K L).bar (hyperbolicMiddlePairing h x y z w) =
      hyperbolicMiddlePairing h x y w z :=
  hbar z w

variable {h} {x y : V}
  (hxx : h x x = 0) (hxy : h x y = 1) (hyx : h y x = 1) (hyy : h y y = 0)

include hbar hxx hxy hyx hyy in
/-- Removing an actual hyperbolic plane retains nondegeneracy. -/
theorem hyperbolicMiddlePairing_nondegenerate (hn : h.Nondegenerate) :
    (hyperbolicMiddlePairing h x y).Nondegenerate := by
  have hleft : ∀ z : hyperbolicMiddle h x y,
      (∀ w, hyperbolicMiddlePairing h x y z w = 0) → z = 0 := by
    intro z hz
    apply Subtype.ext
    apply hn.1 (z : V)
    intro v
    have hzx : h (z : V) x = 0 := z.property.1
    have hzy : h (z : V) y = 0 := z.property.2
    have hp := hyperbolicCoordinates_pairing hbar hxx hxy hyx hyy (z : V) v
    have hzproj : hyperbolicProjection hxx hxy hyx hyy (z : V) = z := by
      apply Subtype.ext
      simp only [hyperbolicProjection_val, hzx, hzy,
        zero_smul, sub_zero]
    change h (z : V) v =
      h (z : V) y * (fieldInvolution K L).bar (h v x) +
        h (hyperbolicProjection hxx hxy hyx hyy (z : V) : V)
          (hyperbolicProjection hxx hxy hyx hyy v : V) +
        h (z : V) x * (fieldInvolution K L).bar (h v y) at hp
    rw [hzx, hzy, hzproj, zero_mul, zero_add, zero_mul,
      add_zero] at hp
    exact hp.trans (hz (hyperbolicProjection hxx hxy hyx hyy v))
  refine ⟨hleft, ?_⟩
  intro z hz
  apply hleft z
  intro w
  rw [hyperbolicMiddlePairing_apply, ← hbar (w : V) (z : V)]
  change (fieldInvolution K L).bar (hyperbolicMiddlePairing h x y w z) = 0
  rw [hz w, map_zero]

/-- The actual intersection with an isotropic submodule, regarded as a submodule
of the hyperbolic middle. -/
def isotropicMiddle (W : Submodule L V) : Submodule L (hyperbolicMiddle h x y) :=
  W.comap (hyperbolicMiddle h x y).subtype

variable (W : Submodule L V)
  (hW : ∀ a b : W, h (a : V) (b : V) = 0) (hxW : x ∈ W)

/-- Hyperbolic projection of a totally isotropic submodule containing the first
hyperbolic vector stays in the actual intersection with the middle. -/
def isotropicHyperbolicProjection : W →ₗ[L] isotropicMiddle (h := h) (x := x) (y := y) W :=
  ((hyperbolicProjection hxx hxy hyx hyy).comp W.subtype).codRestrict _ (by
    intro z
    change (hyperbolicProjection hxx hxy hyx hyy (z : V) : V) ∈ W
    rw [hyperbolicProjection_val, show h (z : V) x = 0 from hW z ⟨x, hxW⟩,
      zero_smul, sub_zero]
    exact W.sub_mem z.property (W.smul_mem _ hxW))

/-- An actual totally isotropic submodule containing the first hyperbolic
vector is the direct sum of that line and its intersection with the middle. -/
def isotropicHyperbolicCoordinates :
    W ≃ₗ[L] L × isotropicMiddle (h := h) (x := x) (y := y) W where
  toLinearMap := ((h.flip y).comp W.subtype).prod
    (isotropicHyperbolicProjection hxx hxy hyx hyy W hW hxW)
  invFun z := ⟨z.1 • x + ((z.2 : hyperbolicMiddle h x y) : V),
    W.add_mem (W.smul_mem _ hxW) z.2.property⟩
  left_inv z := by
    apply Subtype.ext
    change h (z : V) y • x +
      ((z : V) - h (z : V) y • x - h (z : V) x • y) = z
    rw [show h (z : V) x = 0 from hW z ⟨x, hxW⟩, zero_smul, sub_zero]
    abel
  right_inv z := by
    rcases z with ⟨a, z⟩
    have hzx : h ((z : hyperbolicMiddle h x y) : V) x = 0 := z.val.property.1
    have hzy : h ((z : hyperbolicMiddle h x y) : V) y = 0 := z.val.property.2
    have ha : h (a • x + ((z : hyperbolicMiddle h x y) : V)) y = a := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, hxy, hzy, mul_one, add_zero]
    have hb : h (a • x + ((z : hyperbolicMiddle h x y) : V)) x = 0 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, hxx, hzx, mul_zero, add_zero]
    apply Prod.ext
    · exact ha
    · apply Subtype.ext
      apply Subtype.ext
      change a • x + ((z : hyperbolicMiddle h x y) : V) -
        h (a • x + ((z : hyperbolicMiddle h x y) : V)) y • x -
        h (a • x + ((z : hyperbolicMiddle h x y) : V)) x • y = z
      rw [ha, hb, zero_smul, sub_zero]
      abel

include hxx hxy hyx hyy hW hxW in
/-- Removing the hyperbolic plane lowers this actual isotropic dimension by one. -/
theorem isotropicMiddle_finrank [FiniteDimensional L V] :
    Module.finrank L W =
      Module.finrank L (isotropicMiddle (h := h) (x := x) (y := y) W) + 1 := by
  have hd := (isotropicHyperbolicCoordinates hxx hxy hyx hyy W hW hxW).finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_self, add_comm] using hd

include hW in
/-- The actual intersection remains totally isotropic for the restricted pairing. -/
theorem isotropicMiddle_totallyIsotropic
    (z w : isotropicMiddle (h := h) (x := x) (y := y) W) :
    hyperbolicMiddlePairing h x y (z : hyperbolicMiddle h x y)
      (w : hyperbolicMiddle h x y) = 0 :=
  hW ⟨((z : hyperbolicMiddle h x y) : V), z.property⟩
    ⟨((w : hyperbolicMiddle h x y) : V), w.property⟩

private theorem isotropic_dimension_bound_aux (n : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
      (h : V →ₗ[L] V →ₛₗ[(fieldInvolution K L).bar.toRingHom] L)
      (_hbar : ∀ x y, (fieldInvolution K L).bar (h x y) = h y x)
      (_hn : h.Nondegenerate) (W : Submodule L V)
      (_hW : ∀ a b : W, h (a : V) (b : V) = 0),
      Module.finrank L V = n → 2 * Module.finrank L W ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ h hbar hn W hW hdim
    by_cases hW0 : W = ⊥
    · subst W
      simp only [finrank_bot, mul_zero, zero_le]
    obtain ⟨x, hxW, hx⟩ := (Submodule.ne_bot_iff W).mp hW0
    have hxx : h x x = 0 := hW ⟨x, hxW⟩ ⟨x, hxW⟩
    obtain ⟨y, hxy, hyx, hyy⟩ := exists_hyperbolic_partner h hbar hn hx hxx
    have hd := hyperbolicMiddle_finrank hxx hxy hyx hyy
    have hlt : Module.finrank L (hyperbolicMiddle h x y) < n := by omega
    have hb := ih (Module.finrank L (hyperbolicMiddle h x y)) hlt
      (hyperbolicMiddlePairing h x y)
      (hyperbolicMiddlePairing_bar h hbar x y)
      (hyperbolicMiddlePairing_nondegenerate hbar hxx hxy hyx hyy hn)
      (isotropicMiddle (h := h) (x := x) (y := y) W)
      (isotropicMiddle_totallyIsotropic W hW) rfl
    have hw := isotropicMiddle_finrank hxx hxy hyx hyy W hW hxW
    omega

include hbar hW in
/-- A totally isotropic submodule of a nondegenerate Hermitian space has at most
half the ambient dimension, in every characteristic. -/
theorem two_mul_finrank_le_of_totallyIsotropic [FiniteDimensional L V]
    (hn : h.Nondegenerate) :
    2 * Module.finrank L W ≤ Module.finrank L V :=
  isotropic_dimension_bound_aux (Module.finrank L V) h hbar hn W hW rfl

include hbar hW in
/-- In ambient dimension at most three, every totally isotropic submodule has
dimension at most one. -/
theorem finrank_le_one_of_totallyIsotropic_of_finrank_le_three
    [FiniteDimensional L V] (hn : h.Nondegenerate)
    (hdim : Module.finrank L V ≤ 3) : Module.finrank L W ≤ 1 := by
  have hb := two_mul_finrank_le_of_totallyIsotropic hbar W hW hn
  omega

end Langlands.GroupScheme.HermitianRoot
