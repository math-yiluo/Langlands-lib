import Langlands.Representation.Derivative.MinusVanishing
import Langlands.Representation.Unitary.Basic
import Langlands.LocalField.Uniformizer

/-!
# Radical averages contract uniformizer eigenvalues on radical coinvariants

Let `ρ` be a smooth unitarizable representation of the mirabolic group `P_(m+2)` with no
nonzero vector fixed by its radical `V ≅ F^(m+1)`. If the class of `y` in the
`V`-coinvariants is nonzero and is an eigenvector, with eigenvalue `c`, of the Levi scalar
`z = diag(ϖ, …, ϖ, 1)`, then `‖c‖ < 1`. This is the analytic core of Bernstein 1984,
§7.3–7.4. See the paired Markdown for the averaging argument.
-/

noncomputable section

namespace Langlands.Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis Jacquet.Localization

universe uF uV

/-! ## Orthogonality of orbit means -/

section Orthogonal

variable {H : Type*} [Group H] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- For a form preserved by `σ`, a vector is orthogonal to its distance from its orbit
mean, so `re ⟪v, v⟫` splits as a sum of the two squared lengths. -/
theorem re_inner_self_eq_orbitMean_add (c : InnerProductSpace.Core ℂ V)
    (σ : Representation ℂ H V) (hσ : ∀ h v w, c.inner (σ h v) (σ h w) = c.inner v w)
    (v : V) [Finite (Compact.orbit σ v)] :
    (c.inner v v).re = (c.inner (Compact.orbitMean σ v) (Compact.orbitMean σ v)).re +
      (c.inner (v - Compact.orbitMean σ v) (v - Compact.orbitMean σ v)).re := by
  let : InnerProductSpace.Core ℂ V := c
  set a := Compact.orbitMean σ v
  let ℓ : V →ₗ[ℂ] ℂ :=
    { toFun := fun w => c.inner a w
      map_add' := fun x y => InnerProductSpace.Core.inner_add_right (𝕜 := ℂ) a x y
      map_smul' := fun r x => InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ) a x }
  have horth : c.inner a (v - a) = 0 := by
    have hmem := sub_orbitMean_mem σ v (LinearMap.ker ℓ) fun g => by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      change c.inner a v = c.inner a (σ g v)
      have h := hσ g a v
      rw [show σ g a = a from Compact.orbitMean_invariant σ v g] at h
      exact h.symm
    exact hmem
  have horth' : c.inner (v - a) a = 0 := by
    have h := InnerProductSpace.Core.inner_conj_symm (𝕜 := ℂ) (v - a) a
    change (starRingEnd ℂ) (c.inner a (v - a)) = c.inner (v - a) a at h
    rw [← h, horth, map_zero]
  have hadd := InnerProductSpace.Core.inner_add_add_self (𝕜 := ℂ) a (v - a)
  change c.inner (a + (v - a)) (a + (v - a)) =
    c.inner a a + c.inner a (v - a) + c.inner (v - a) a + c.inner (v - a) (v - a) at hadd
  rw [add_sub_cancel, horth, horth', add_zero, add_zero] at hadd
  rw [hadd, Complex.add_re]

/-- Scaling multiplies `re ⟪x, x⟫` by `‖r‖ ^ 2`. -/
theorem re_inner_smul_self (c : InnerProductSpace.Core ℂ V) (r : ℂ) (x : V) :
    (c.inner (r • x) (r • x)).re = ‖r‖ ^ 2 * (c.inner x x).re := by
  let : InnerProductSpace.Core ℂ V := c
  have h1 := InnerProductSpace.Core.inner_smul_left (𝕜 := ℂ) x (r • x) (r := r)
  have h2 := InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ) x x (r := r)
  change c.inner (r • x) (r • x) = (starRingEnd ℂ) r * c.inner x (r • x) at h1
  change c.inner x (r • x) = r * c.inner x x at h2
  rw [h1, h2, ← mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow, Complex.re_ofReal_mul]

/-- `re ⟪x, x⟫ = 0` forces `x = 0` for a positive definite form. -/
theorem eq_zero_of_re_inner_self_eq_zero (c : InnerProductSpace.Core ℂ V) {x : V}
    (hx : (c.inner x x).re = 0) : x = 0 := by
  let : InnerProductSpace.Core ℂ V := c
  have him := InnerProductSpace.Core.inner_self_im (𝕜 := ℂ) x
  change (c.inner x x).im = 0 at him
  exact c.definite x (Complex.ext hx him)

end Orthogonal

/-! ## The uniformizer shifts radical boxes -/

section Shift

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

theorem uniformizer_mul_mem_additiveLattice {k : ℤ} {x : F.Carrier}
    (hx : x ∈ T.additiveLattice (k + 1)) : T.uniformizer * x ∈ T.additiveLattice k := by
  rw [PadicField.TopologicalData.mem_additiveLattice] at hx ⊢
  rw [map_mul, T.discreteValuation_uniformizer]
  calc WithZero.exp (-1) * T.discreteValuation x
      ≤ WithZero.exp (-1) * WithZero.exp (k + 1) := mul_le_mul_right hx _
    _ = WithZero.exp k := by rw [← WithZero.exp_add]; congr 1; ring

theorem uniformizer_inv_mul_mem_additiveLattice {k : ℤ} {x : F.Carrier}
    (hx : x ∈ T.additiveLattice k) : T.uniformizer⁻¹ * x ∈ T.additiveLattice (k + 1) := by
  rw [PadicField.TopologicalData.mem_additiveLattice] at hx ⊢
  rw [map_mul, map_inv₀, T.discreteValuation_uniformizer, ← WithZero.exp_neg, neg_neg]
  calc WithZero.exp 1 * T.discreteValuation x
      ≤ WithZero.exp 1 * WithZero.exp k := mul_le_mul_right hx _
    _ = WithZero.exp (k + 1) := by rw [← WithZero.exp_add, add_comm]

/-- Conjugation by the Levi scalar `diag(a, …, a, 1)` scales the radical coordinates. -/
theorem levi_scalar_conjugate_radicalElement {n : ℕ} (a : F.Carrierˣ)
    (v : Fin n → F.Carrier) :
    levi (scalar a) * (radicalElement v).val * (levi (scalar a))⁻¹ =
      (radicalElement ((a : F.Carrier) • v)).val := by
  rw [levi_conjugate_radicalElement]
  congr 2
  funext j
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

end Shift

/-! ## Contraction -/

section Contraction

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Bernstein 1984, §7.3–7.4: on a smooth unitarizable representation of `P_(m+2)`
without nonzero radical-fixed vectors, every eigenvalue `c` of the Levi scalar
`diag(ϖ, …, ϖ, 1)` on a nonzero radical-coinvariant class satisfies `‖c‖ < 1`. -/
theorem norm_lt_one_of_radical_eigen (m : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (mirabolic (m + 1) F.Carrier) V) :
    letI := T.topology
    haveI := T.generalLinearTopologicalGroup (m + 1 + 1)
    IsSmooth ρ → IsUnitarizable ρ →
      (∀ v : V, (∀ u : radical (m + 1) F.Carrier, ρ u v = v) → v = 0) →
      ∀ (y : V) (c : ℂ), y ∉ relations ρ (radical (m + 1) F.Carrier) 1 →
        ρ (levi (scalar (LocalFactor.PadicAbelian.uniformizerUnit T))) y - c • y ∈
          relations ρ (radical (m + 1) F.Carrier) 1 →
        ‖c‖ < 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.generalLinearTopologicalGroup (m + 1 + 1)
  intro hρ hu hfix y c hy hc
  obtain ⟨b⟩ := hu
  let N := radical (m + 1) F.Carrier
  have hχ : IsOpen ((1 : N →* ℂˣ).ker : Set N) := by
    rw [MonoidHom.ker_one]
    exact isOpen_univ
  let S : ℕ → OpenSubgroup N := fun k => radicalBox T m k
  have hS : ∀ k, IsCompact (S k : Set N) := fun k => isCompact_radicalBox T m k
  have hmono : Monotone S := fun j k hjk => radicalBox_mono T m (Nat.cast_le.mpr hjk)
  have hcover : ∀ u : N, ∃ k, u ∈ S k := by
    intro u
    obtain ⟨M, hM⟩ := exists_mem_latticeBox T (radicalCoordinates u)
    exact ⟨M.toNat, radicalBox_mono T m (Int.self_le_toNat M) hM⟩
  let A : ℕ → V →ₗ[ℂ] V := fun k => characterAverage hρ hχ (S k) (hS k)
  have htr : ∀ (u : N) (v : V), twistedRestriction ρ N 1 u v = ρ u v := by
    intro u v
    rw [twistedRestriction_apply, MonoidHom.one_apply, Units.val_one, inv_one, one_smul]
  -- Averages are fixed by their box, fix fixed vectors, and absorb box translations.
  have hAfix : ∀ k x (u : N), u ∈ S k → ρ u (A k x) = A k x := by
    intro k x u hu
    have h := Compact.averageMap_mem_fixedVectors (twistedRestriction ρ N 1)
      (isSmooth_twistedRestriction hρ hχ) (S k) (hS k) x
    have h' := (Representation.mem_invariants _ _).mp h ⟨u, hu⟩
    change twistedRestriction ρ N 1 u (A k x) = A k x at h'
    rwa [htr] at h'
  have hAid : ∀ k x, (∀ u : N, u ∈ S k → ρ u x = x) → A k x = x := by
    intro k x hx
    refine Compact.averageMap_id (twistedRestriction ρ N 1) (isSmooth_twistedRestriction hρ hχ)
      (S k) (hS k) x ?_
    refine (Representation.mem_invariants _ _).mpr fun u => ?_
    change twistedRestriction ρ N 1 u x = x
    rw [htr]
    exact hx u u.property
  have hAinv : ∀ k x (u : N), u ∈ S k → A k (ρ u x) = A k x := by
    intro k x u hu
    have h := characterAverage_relation hρ hχ (S k) (hS k) hu x
    rwa [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, sub_eq_zero] at h
  have hArel : ∀ k x, x - A k x ∈ relations ρ N 1 := fun k x =>
    sub_characterAverage_mem hρ hχ (S k) (hS k) x
  -- Averages over nested boxes.
  have hnest : ∀ k x, A (k + 1) (A k x) = A (k + 1) x := by
    intro k x
    have hidem : A k (x - A k x) = 0 := by
      rw [map_sub, hAid k (A k x) (fun u hu => hAfix k x u hu), sub_self]
    have h := characterAverage_eq_zero_of_le hρ hχ (hS k) (hS (k + 1))
      (hmono (Nat.le_succ k)) hidem
    change A (k + 1) (x - A k x) = 0 at h
    rw [map_sub, sub_eq_zero] at h
    exact h.symm
  -- The Levi scalar shifts the boxes.
  set ϖ := LocalFactor.PadicAbelian.uniformizerUnit T with hϖ
  set z : mirabolic (m + 1) F.Carrier := levi (scalar ϖ) with hz
  have hzinv : z⁻¹ = levi (scalar ϖ⁻¹) := by rw [hz, map_inv, map_inv]
  have hconj : ∀ k (u : N), u ∈ S (k + 1) → ∃ u' : N, u' ∈ S k ∧
      z * (u : mirabolic (m + 1) F.Carrier) * z⁻¹ = u' := by
    intro k u hu
    refine ⟨radicalElement ((ϖ : F.Carrier) • radicalCoordinates u), ?_, ?_⟩
    · change radicalCoordinates (radicalElement ((ϖ : F.Carrier) • radicalCoordinates u)) ∈
        latticeBox T (m + 1) (k : ℤ)
      rw [radicalCoordinates_element]
      refine (mem_latticeBox T).mpr fun j => ?_
      have hj := (mem_latticeBox T).mp hu j
      push_cast at hj
      exact uniformizer_mul_mem_additiveLattice T hj
    · conv_lhs => rw [← radicalElement_coordinates u]
      exact levi_scalar_conjugate_radicalElement ϖ _
  have hconj' : ∀ k (u : N), u ∈ S k → ∃ u' : N, u' ∈ S (k + 1) ∧
      z⁻¹ * (u : mirabolic (m + 1) F.Carrier) * z = u' := by
    intro k u hu
    refine ⟨radicalElement (((ϖ⁻¹ : F.Carrierˣ) : F.Carrier) • radicalCoordinates u), ?_, ?_⟩
    · change radicalCoordinates (radicalElement
          (((ϖ⁻¹ : F.Carrierˣ) : F.Carrier) • radicalCoordinates u)) ∈
        latticeBox T (m + 1) ((k + 1 : ℕ) : ℤ)
      rw [radicalCoordinates_element]
      refine (mem_latticeBox T).mpr fun j => ?_
      have hj := (mem_latticeBox T).mp hu j
      push_cast
      rw [Pi.smul_apply, smul_eq_mul, hϖ,
        LocalFactor.PadicAbelian.uniformizerUnit_coe]
      exact uniformizer_inv_mul_mem_additiveLattice T hj
    · have hz' : z = (levi (scalar ϖ⁻¹))⁻¹ := by rw [← hzinv, inv_inv]
      conv_lhs => rw [hzinv, hz', ← radicalElement_coordinates u]
      exact levi_scalar_conjugate_radicalElement ϖ⁻¹ _
  have hρmul : ∀ (g h : mirabolic (m + 1) F.Carrier) (w : V), ρ g (ρ h w) = ρ (g * h) w :=
    fun g h w => by rw [map_mul, Module.End.mul_apply]
  -- The averages intertwine through the Levi scalar.
  have hcomm : ∀ k x, ρ z (A (k + 1) x) = A k (ρ z x) := by
    intro k x
    have hw1 : ∀ u : N, u ∈ S k → ρ u (ρ z (A (k + 1) x)) = ρ z (A (k + 1) x) := by
      intro u hu
      obtain ⟨u', hu', he⟩ := hconj' k u hu
      calc ρ u (ρ z (A (k + 1) x))
          = ρ z (ρ (z⁻¹ * (u : mirabolic (m + 1) F.Carrier) * z) (A (k + 1) x)) := by
            rw [hρmul, hρmul, ← mul_assoc, mul_inv_cancel_left]
        _ = ρ z (A (k + 1) x) := by rw [he, hAfix (k + 1) x u' hu']
    have h1 : A k (ρ z (A (k + 1) x)) = ρ z (A (k + 1) x) := hAid k _ hw1
    have h2 : A k (ρ z (x - A (k + 1) x)) = 0 := by
      let := finite_orbit_twistedRestriction hρ hχ (S (k + 1)) (hS (k + 1)) x
      have hmem := sub_orbitMean_mem
        ((twistedRestriction ρ N 1).comp (S (k + 1)).toSubgroup.subtype) x
        (LinearMap.ker (A k ∘ₗ ρ z)) fun h => by
          rw [LinearMap.mem_ker]
          change A k (ρ z (x - twistedRestriction ρ N 1 (h : N) x)) = 0
          rw [htr]
          obtain ⟨u', hu', he⟩ := hconj k (h : N) h.property
          have hzu : ρ z (ρ ((h : N) : mirabolic (m + 1) F.Carrier) x) = ρ u' (ρ z x) := by
            rw [← he, hρmul, hρmul, inv_mul_cancel_right]
          rw [map_sub, map_sub, hzu, hAinv k _ u' hu', sub_self]
      exact hmem
    rw [map_sub, map_sub, h1, sub_eq_zero] at h2
    exact h2.symm
  -- The quadratic form.
  let Q : V → ℝ := fun x => (b.inner x x).re
  have hQinv : ∀ (g : mirabolic (m + 1) F.Carrier) x, Q (ρ g x) = Q x := fun g x => by
    change (b.inner (ρ g x) (ρ g x)).re = (b.inner x x).re
    rw [b.invariant]
  have hQnn : ∀ x, 0 ≤ Q x := fun x => b.re_inner_nonneg x
  have hpyth : ∀ k x, Q x = Q (A k x) + Q (x - A k x) := by
    intro k x
    let := finite_orbit_twistedRestriction hρ hχ (S k) (hS k) x
    refine re_inner_self_eq_orbitMean_add b.toInnerProductCore
      ((twistedRestriction ρ N 1).comp (S k).toSubgroup.subtype) (fun h v w => ?_) x
    change b.inner (twistedRestriction ρ N 1 (h : N) v)
      (twistedRestriction ρ N 1 (h : N) w) = b.inner v w
    rw [htr, htr]
    exact b.invariant _ v w
  -- Conclusion.
  by_contra hlt
  push Not at hlt
  obtain ⟨k₀, hk₀⟩ := eventually_characterAverage_eq_zero hρ hχ S hS hmono hcover hc
  have hstep : ∀ k, k₀ ≤ k → A (k + 1) y = A k y := by
    intro k hk
    have h1 : ρ z (A (k + 1) y) = c • A k y := by
      have h := hk₀ k hk
      change A k (ρ z y - c • y) = 0 at h
      rw [map_sub, map_smul, sub_eq_zero] at h
      rw [hcomm, h]
    have hQ : Q (A (k + 1) y) = ‖c‖ ^ 2 * Q (A k y) := by
      rw [← hQinv z, h1]
      exact re_inner_smul_self b.toInnerProductCore c _
    have hp := hpyth (k + 1) (A k y)
    rw [hnest, hQ] at hp
    have hc1 : 1 ≤ ‖c‖ ^ 2 := one_le_pow₀ hlt
    have hnn1 := hQnn (A k y)
    have hnn2 := hQnn (A k y - A (k + 1) y)
    have hzero : Q (A k y - A (k + 1) y) = 0 := by nlinarith
    exact (sub_eq_zero.mp (eq_zero_of_re_inner_self_eq_zero b.toInnerProductCore hzero)).symm
  have hconst : ∀ k, k₀ ≤ k → A k y = A k₀ y := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih => rw [hstep k hk, ih]
  have hfixall : ∀ u : N, ρ u (A k₀ y) = A k₀ y := by
    intro u
    obtain ⟨k, hk⟩ := hcover u
    have h := hAfix (max k k₀) y u (hmono (le_max_left k k₀) hk)
    rwa [hconst _ (le_max_right k k₀)] at h
  have h0 := hfix _ hfixall
  have hrel := hArel k₀ y
  rw [h0, sub_zero] at hrel
  exact hy hrel

end Contraction

end Langlands.Derivative.Mirabolic
