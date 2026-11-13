import Langlands.GroupScheme.Examples.HermitianRootDiagonalization
import Langlands.GroupScheme.Examples.SU3RootParametersRational

/-! # Hyperbolic splitting and rank-one Hermitian coordinates -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {V : Type v} [AddCommGroup V] [Module L V]
  (h : V →ₗ[L] V →ₛₗ[(fieldInvolution K L).bar.toRingHom] L)
  (hbar : ∀ x y, (fieldInvolution K L).bar (h x y) = h y x)

include hbar in
/-- A nonzero isotropic vector in a nondegenerate Hermitian space has an
isotropic partner with both cross pairings equal to one, in every characteristic. -/
theorem exists_hyperbolic_partner (hn : h.Nondegenerate) {x : V}
    (hx : x ≠ 0) (hxx : h x x = 0) :
    ∃ y : V, h x y = 1 ∧ h y x = 1 ∧ h y y = 0 := by
  obtain ⟨y, hy⟩ : ∃ y : V, h y x ≠ 0 := by
    by_contra! hy
    exact hx (hn.2 x hy)
  let z : V := (h y x)⁻¹ • y
  have hzx : h z x = 1 := by
    dsimp only [z]
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hy]
  have hxz : h x z = 1 := by
    rw [← hbar z x, hzx, map_one]
  let a : L := traceOne K L * h z z
  have ha : a + (fieldInvolution K L).bar a = h z z := by
    change traceOne K L * h z z +
      (fieldInvolution K L).bar (traceOne K L * h z z) = h z z
    rw [map_mul, hbar z z]
    change traceOne K L * h z z + conjugation K L (traceOne K L) * h z z = h z z
    rw [← add_mul, traceOne_add_conjugate, one_mul]
  refine ⟨z - a • x, ?_, ?_, ?_⟩
  · simp only [map_sub, map_smulₛₗ, smul_eq_mul, hxx, hxz, mul_zero, sub_zero]
  · simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hxx, hzx, mul_zero, sub_zero]
  · simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      map_smulₛₗ, smul_eq_mul, hxx, hxz, hzx, mul_zero, sub_zero,
      mul_one]
    change h z z - a - (fieldInvolution K L).bar a = 0
    linear_combination -ha

/-- The simultaneous orthogonal complement of the two hyperbolic vectors. -/
def hyperbolicMiddle (x y : V) : Submodule L V :=
  (h.flip x).ker ⊓ (h.flip y).ker

@[simp] theorem mem_hyperbolicMiddle (x y z : V) :
    z ∈ hyperbolicMiddle h x y ↔ h z x = 0 ∧ h z y = 0 := Iff.rfl

variable {h} {x y : V}
  (hxx : h x x = 0) (hxy : h x y = 1) (hyx : h y x = 1) (hyy : h y y = 0)

/-- Project off the hyperbolic plane by the two actual cross pairings. -/
def hyperbolicProjection : V →ₗ[L] hyperbolicMiddle h x y :=
  (LinearMap.id - (h.flip y).smulRight x - (h.flip x).smulRight y).codRestrict _ (by
    intro z
    change h (z - h z y • x - h z x • y) x = 0 ∧
      h (z - h z y • x - h z x • y) y = 0
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hxx, hxy, hyx, hyy, mul_zero, mul_one, sub_zero, sub_self,
      and_self])

@[simp] theorem hyperbolicProjection_val (z : V) :
    (hyperbolicProjection hxx hxy hyx hyy z : V) = z - h z y • x - h z x • y := rfl

/-- The full vector space splits into the hyperbolic plane and its actual
orthogonal complement; coordinates are linear over the quadratic field. -/
def hyperbolicCoordinates : V ≃ₗ[L] L × (hyperbolicMiddle h x y × L) where
  toLinearMap := (h.flip y).prod
    ((hyperbolicProjection hxx hxy hyx hyy).prod (h.flip x))
  invFun z := z.1 • x + (z.2.1 : V) + z.2.2 • y
  left_inv z := by
    change h z y • x + (z - h z y • x - h z x • y) + h z x • y = z
    abel
  right_inv z := by
    rcases z with ⟨a, z, b⟩
    have hz := z.property
    change h (z : V) x = 0 ∧ h (z : V) y = 0 at hz
    have ha : h (a • x + (z : V) + b • y) y = a := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, hxy, hyy, hz.2, mul_one, mul_zero, add_zero]
    have hb : h (a • x + (z : V) + b • y) x = b := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, hxx, hyx, hz.1, mul_one, mul_zero, zero_add]
    apply Prod.ext
    · exact ha
    · apply Prod.ext
      · apply Subtype.ext
        change a • x + (z : V) + b • y -
          h (a • x + (z : V) + b • y) y • x -
          h (a • x + (z : V) + b • y) x • y = z
        rw [ha, hb]
        abel
      · exact hb

include hbar in
/-- In the inverse product coordinates the full pairing is the sum of the
two hyperbolic cross terms and the restricted middle pairing. -/
theorem hyperbolicCoordinates_symm_pairing
    (p q : L × (hyperbolicMiddle h x y × L)) :
    h ((hyperbolicCoordinates hxx hxy hyx hyy).symm p)
        ((hyperbolicCoordinates hxx hxy hyx hyy).symm q) =
      p.1 * (fieldInvolution K L).bar q.2.2 +
        h (p.2.1 : V) (q.2.1 : V) +
        p.2.2 * (fieldInvolution K L).bar q.1 := by
  have hpx : h (p.2.1 : V) x = 0 := p.2.1.property.1
  have hpy : h (p.2.1 : V) y = 0 := p.2.1.property.2
  have hqx : h (q.2.1 : V) x = 0 := q.2.1.property.1
  have hqy : h (q.2.1 : V) y = 0 := q.2.1.property.2
  have hxq : h x (q.2.1 : V) = 0 := by
    rw [← hbar (q.2.1 : V) x, hqx, map_zero]
  have hyq : h y (q.2.1 : V) = 0 := by
    rw [← hbar (q.2.1 : V) y, hqy, map_zero]
  change h (p.1 • x + (p.2.1 : V) + p.2.2 • y)
    (q.1 • x + (q.2.1 : V) + q.2.2 • y) = _
  simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hxx, hxy, hyx, hyy,
    hpx, hpy, hxq, hyq, mul_zero, mul_one,
    add_zero, zero_add]
  change (fieldInvolution K L).bar q.1 * p.2.2 +
    h (p.2.1 : V) (q.2.1 : V) +
    (fieldInvolution K L).bar q.2.2 * p.1 = _
  ring

include hbar in
/-- The explicit linear coordinates preserve the entire Hermitian pairing. -/
theorem hyperbolicCoordinates_pairing (v w : V) :
    let e := hyperbolicCoordinates hxx hxy hyx hyy
    h v w = (e v).1 * (fieldInvolution K L).bar (e w).2.2 +
      h ((e v).2.1 : V) ((e w).2.1 : V) +
      (e v).2.2 * (fieldInvolution K L).bar (e w).1 := by
  dsimp only
  simpa only [LinearEquiv.symm_apply_apply] using
    hyperbolicCoordinates_symm_pairing hbar hxx hxy hyx hyy
      (hyperbolicCoordinates hxx hxy hyx hyy v)
      (hyperbolicCoordinates hxx hxy hyx hyy w)

include hxx hxy hyx hyy in
/-- Splitting off a hyperbolic plane lowers the finite dimension by two. -/
theorem hyperbolicMiddle_finrank [FiniteDimensional L V] :
    Module.finrank L V = Module.finrank L (hyperbolicMiddle h x y) + 2 := by
  have hd := (hyperbolicCoordinates hxx hxy hyx hyy).finrank_eq
  simp only [Module.finrank_prod, Module.finrank_self] at hd
  omega

include hbar hxx hxy in
/-- A Hermitian space with no totally isotropic submodule of dimension two
has anisotropic complement to a hyperbolic plane. -/
theorem hyperbolicMiddle_isAnisotropic [FiniteDimensional L V]
    (hrank : ∀ W : Submodule L V,
      (∀ a b : W, h (a : V) (b : V) = 0) → Module.finrank L W ≤ 1) :
    ∀ z : hyperbolicMiddle h x y, h (z : V) (z : V) = 0 → z = 0 := by
  intro z hzz
  by_contra hz
  have hz0 : (z : V) ≠ 0 := fun hh => hz (Subtype.ext hh)
  have hzx : h (z : V) x = 0 := z.property.1
  have hzy : h (z : V) y = 0 := z.property.2
  have hxz : h x (z : V) = 0 := by rw [← hbar (z : V) x, hzx, map_zero]
  let f : (L × L) →ₗ[L] V :=
    (LinearMap.fst L L L).smulRight x + (LinearMap.snd L L L).smulRight (z : V)
  have hfval (p : L × L) : f p = p.1 • x + p.2 • (z : V) := rfl
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro p hp
    have hp1 : p.1 = 0 := by
      have ht := congrArg (fun w => h w y) hp
      rw [hfval] at ht
      simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, hxy, hzy, mul_one, mul_zero, add_zero, map_zero,
        LinearMap.zero_apply] using ht
    have hp2 : p.2 = 0 := by
      rw [hfval, hp1, zero_smul, zero_add] at hp
      exact (smul_eq_zero.mp hp).resolve_right hz0
    exact Prod.ext hp1 hp2
  have ht : ∀ a b : f.range, h (a : V) (b : V) = 0 := by
    intro a b
    obtain ⟨p, hp⟩ := a.property
    obtain ⟨q, hq⟩ := b.property
    rw [← hp, ← hq, hfval, hfval]
    simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, hxx, hzz, hzx, hxz, mul_zero,
      add_zero]
  have hb := hrank f.range ht
  rw [LinearMap.finrank_range_of_inj hf] at hb
  simp only [Module.finrank_prod, Module.finrank_self] at hb
  omega

/-- The negative restricted middle pairing matches the sign convention
of `HermitianRoot.gram`. -/
def negativeMiddlePairing (h :
    V →ₗ[L] V →ₛₗ[(fieldInvolution K L).bar.toRingHom] L) (x y : V) :
    hyperbolicMiddle h x y →ₗ[L]
      hyperbolicMiddle h x y →ₛₗ[(fieldInvolution K L).bar.toRingHom] L :=
  -(h.domRestrict₁₂ (hyperbolicMiddle h x y) (hyperbolicMiddle h x y))

@[simp] theorem negativeMiddlePairing_apply
    (p q : hyperbolicMiddle h x y) :
    negativeMiddlePairing h x y p q = -h (p : V) (q : V) := rfl

include hbar in
/-- Negating and restricting a Hermitian pairing retains Hermitian symmetry. -/
theorem negativeMiddlePairing_bar (p q : hyperbolicMiddle h x y) :
    (fieldInvolution K L).bar (negativeMiddlePairing h x y p q) =
      negativeMiddlePairing h x y q p := by
  simp only [negativeMiddlePairing_apply, map_neg, hbar]

include hbar hxx hxy in
/-- The negative restricted middle form is anisotropic under the actual
total-isotropic-submodule dimension bound. -/
theorem negativeMiddlePairing_isAnisotropic [FiniteDimensional L V]
    (hrank : ∀ W : Submodule L V,
      (∀ a b : W, h (a : V) (b : V) = 0) → Module.finrank L W ≤ 1) :
    ∀ z : hyperbolicMiddle h x y, negativeMiddlePairing h x y z z = 0 → z = 0 := by
  intro z hz
  apply hyperbolicMiddle_isAnisotropic hbar hxx hxy hrank z
  exact neg_eq_zero.mp hz

include hbar in
/-- A nondegenerate Hermitian space of Witt index one has explicit linear
coordinates with one hyperbolic plane and a negative anisotropic diagonal middle.
The rank-one hypothesis is expressed by actual totally isotropic submodules. -/
theorem exists_rankOne_diagonal_coordinates [FiniteDimensional L V]
    (hn : h.Nondegenerate) {x : V} (hx : x ≠ 0) (hxx : h x x = 0)
    (hrank : ∀ W : Submodule L V,
      (∀ a b : W, h (a : V) (b : V) = 0) → Module.finrank L W ≤ 1)
    (m : ℕ) (hdim : Module.finrank L V = m + 2) :
    ∃ H : DiagonalForm (fieldInvolution K L) (Fin m), H.IsAnisotropic ∧
      ∃ e : V ≃ₗ[L] L × ((Fin m → L) × L), ∀ v w,
        h v w = (e v).1 * (fieldInvolution K L).bar (e w).2.2 -
          H.pairing (e v).2.1 (e w).2.1 +
          (e v).2.2 * (fieldInvolution K L).bar (e w).1 := by
  obtain ⟨y, hxy, hyx, hyy⟩ := exists_hyperbolic_partner h hbar hn hx hxx
  have hm : Module.finrank L (hyperbolicMiddle h x y) = m := by
    have hd := hyperbolicMiddle_finrank hxx hxy hyx hyy
    omega
  have hdiag := exists_anisotropic_diagonal_coordinates
    (negativeMiddlePairing h x y) (negativeMiddlePairing_bar hbar)
    (negativeMiddlePairing_isAnisotropic hbar hxx hxy hrank)
  rw [hm] at hdiag
  obtain ⟨H, hH, f, hf⟩ := hdiag
  let e₀ := hyperbolicCoordinates hxx hxy hyx hyy
  let e := e₀.trans ((LinearEquiv.refl L L).prodCongr
    (f.prodCongr (LinearEquiv.refl L L)))
  refine ⟨H, hH, e, ?_⟩
  intro v w
  have hp := hyperbolicCoordinates_pairing hbar hxx hxy hyx hyy v w
  have hf' := hf (e₀ v).2.1 (e₀ w).2.1
  change H.pairing (f (e₀ v).2.1) (f (e₀ w).2.1) =
    -h ((e₀ v).2.1 : V) ((e₀ w).2.1 : V) at hf'
  change h v w = (e₀ v).1 * (fieldInvolution K L).bar (e₀ w).2.2 -
    H.pairing (f (e₀ v).2.1) (f (e₀ w).2.1) +
    (e₀ v).2.2 * (fieldInvolution K L).bar (e₀ w).1
  rw [hf', sub_neg_eq_add]
  exact hp

end Langlands.GroupScheme.HermitianRoot
