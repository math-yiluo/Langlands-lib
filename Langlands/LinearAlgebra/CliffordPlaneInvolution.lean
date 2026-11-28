import Langlands.LinearAlgebra.CliffordSpinLift

/-! # Clifford lifts of the negation of a nondegenerate plane -/

noncomputable section

universe u v

namespace Langlands.QuadraticForm

open QuadraticMap CliffordAlgebra

variable {F : Type u} {V : Type v} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] [Invertible (2 : F)] (Q : QuadraticForm F V)

namespace CliffordSpinLift

/-- Let `Q` be a quadratic form with nondegenerate polar pairing on a finite-dimensional
space over a field of characteristic different from two. Suppose the vector action `ℓ` of
a Clifford spin lift `s` is a nonidentity involution and the range of `ℓ - id` has dimension
at most two. Then the Clifford unit of `s` squares to `-1`. Geometrically, `ℓ` negates a
nondegenerate plane and fixes its orthogonal complement. -/
theorem unit_mul_unit_eq_neg_one_of_involution (hQ : Q.polarBilin.Nondegenerate)
    (s : CliffordSpinLift Q)
    (h2 : ∀ v, vectorAction Q s (vectorAction Q s v) = v)
    (hne : ∃ v, vectorAction Q s v ≠ v)
    (hrank : Module.finrank F
      (LinearMap.range ((vectorAction Q s : V ≃ₗ[F] V).toLinearMap - LinearMap.id)) ≤ 2) :
    (unit Q s : CliffordAlgebra Q) * unit Q s = -1 := by
  classical
  set ℓ := vectorAction Q s with hℓdef
  set W := LinearMap.range ((ℓ : V ≃ₗ[F] V).toLinearMap - LinearMap.id) with hWdef
  have h2F : (2 : F) ≠ 0 := (isUnit_of_invertible (2 : F)).ne_zero
  have hpres (v w : V) : polar Q (ℓ v) (ℓ w) = polar Q v w := by
    simp only [polar, ← map_add, hℓdef, vectorAction_preserves]
  have hmemW (v : V) : ℓ v - v ∈ W := ⟨v, rfl⟩
  have hneg (w : V) (hw : w ∈ W) : ℓ w = -w := by
    obtain ⟨v, rfl⟩ := hw
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, map_sub, h2]
    abel
  have hperp (u : V) (hu : ℓ u = u) (w : V) (hw : w ∈ W) : polar Q u w = 0 := by
    have h := hpres u w
    rw [hu, hneg w hw, polar_neg_right] at h
    have h' : (2 : F) * polar Q u w = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h').resolve_left h2F
  have hdecomp (v : V) : ∃ u, ℓ u = u ∧ ∃ w ∈ W, v = u + w := by
    refine ⟨(⅟2 : F) • (v + ℓ v), ?_, -(⅟2 : F) • (ℓ v - v), W.smul_mem _ (hmemW v), ?_⟩
    · rw [map_smul, map_add, h2, add_comm]
    · have h22 : (⅟2 : F) + ⅟2 = 1 := by
        rw [← two_mul, mul_invOf_self]
      calc v = ((⅟2 : F) + ⅟2) • v := by rw [h22, one_smul]
        _ = _ := by module
  have hWnd (w : V) (hw : w ∈ W) (h : ∀ w' ∈ W, polar Q w w' = 0) : w = 0 := by
    refine hQ.1 w (fun v => ?_)
    obtain ⟨u, hu, w', hw', rfl⟩ := hdecomp v
    rw [polarBilin_apply_apply, polar_add_right, polar_comm Q w u, hperp u hu w hw, h w' hw',
      add_zero]
  -- An orthogonal basis of `W`.
  let B : LinearMap.BilinForm F W := LinearMap.BilinForm.restrict Q.polarBilin W
  have hBs : LinearMap.IsSymm B := ⟨fun x y => polar_comm Q (x : V) (y : V)⟩
  have hBnd : B.Nondegenerate := by
    refine ⟨fun x hx => Subtype.ext (hWnd x x.2 (fun w' hw' => hx ⟨w', hw'⟩)), fun y hy => ?_⟩
    refine Subtype.ext (hWnd y y.2 (fun w' hw' => ?_))
    rw [polar_comm]
    exact hy ⟨w', hw'⟩
  obtain ⟨c, hc⟩ := LinearMap.BilinForm.exists_orthogonal_basis hBs
  have hcQ (i : Fin (Module.finrank F W)) : Q (c i : V) ≠ 0 := by
    have hn := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate
      (B := B) (v := c) hc hBnd i
    intro hz
    apply hn
    change polar Q (c i : V) (c i : V) = 0
    rw [polar_self, hz, smul_zero]
  have hcorth (i j : Fin (Module.finrank F W)) (hij : i ≠ j) :
      polar Q (c i : V) (c j : V) = 0 := hc hij
  have hpos : 0 < Module.finrank F W := by
    obtain ⟨v, hv⟩ := hne
    exact Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨ℓ v - v, hmemW v⟩, fun h => hv (sub_eq_zero.mp (congrArg Subtype.val h))⟩
  -- The reflection in a vector of `W` fixes the complement and negates the vector.
  have hrefl_perp (u : V) (hu : ℓ u = u) (z : V) (hz : z ∈ W) (hQz : Q z ≠ 0) :
      reflection Q z hQz u = u := by
    rw [reflection_apply, hperp u hu z hz, zero_div, zero_smul, sub_zero]
  have hrefl_self (z : V) (hQz : Q z ≠ 0) : reflection Q z hQz z = -z := by
    rw [reflection_apply, polar_self, nsmul_eq_mul, Nat.cast_ofNat, mul_div_assoc,
      div_self hQz, mul_one, two_smul]
    abel
  have hrefl_orth (z y : V) (hQz : Q z ≠ 0) (hyz : polar Q y z = 0) :
      reflection Q z hQz y = y := by
    rw [reflection_apply, hyz, zero_div, zero_smul, sub_zero]
  rcases (show Module.finrank F W = 1 ∨ Module.finrank F W = 2 by omega) with h1 | h2'
  · -- A one-dimensional `W` would make `ℓ` a reflection, of determinant `-1`.
    exfalso
    let i₀ : Fin (Module.finrank F W) := ⟨0, by omega⟩
    let w₁ : V := c i₀
    have hspan (w : W) : (w : V) = (c.repr w i₀) • w₁ := by
      have h := c.sum_repr w
      have huniv : (Finset.univ : Finset (Fin (Module.finrank F W))) = {i₀} := by
        ext i
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        exact Fin.ext (by omega)
      rw [huniv, Finset.sum_singleton] at h
      exact (congrArg Subtype.val h).symm
    have hℓ : ∀ v, ℓ v = reflection Q w₁ (hcQ i₀) v := by
      intro v
      obtain ⟨u, hu, w, hw, rfl⟩ := hdecomp v
      obtain ⟨a, hab⟩ : ∃ a : F, w = a • w₁ := ⟨_, hspan ⟨w, hw⟩⟩
      rw [map_add, map_add, hu, hrefl_perp u hu w₁ (c i₀).2 (hcQ i₀), hneg w hw, hab, map_smul,
        hrefl_self w₁ (hcQ i₀), smul_neg]
    have hdet := det_vectorAction Q s
    have hlin : (ℓ : V ≃ₗ[F] V).toLinearMap =
        (reflection Q w₁ (hcQ i₀)).toLinearEquiv.toLinearMap := by
      ext v
      exact hℓ v
    have hd : LinearMap.det (ℓ : V ≃ₗ[F] V).toLinearMap = 1 := by
      rw [← LinearEquiv.coe_det]
      exact (congrArg Units.val hdet).trans Units.val_one
    rw [hlin, det_reflection] at hd
    exact h2F (by linear_combination -hd)
  · -- A two-dimensional `W` has an orthogonal basis `w₁, w₂`.
    let i₀ : Fin (Module.finrank F W) := ⟨0, by omega⟩
    let i₁ : Fin (Module.finrank F W) := ⟨1, by omega⟩
    have hi : i₀ ≠ i₁ := fun h => by simpa [i₀, i₁] using congrArg Fin.val h
    let w₁ : V := c i₀
    let w₂ : V := c i₁
    have h12 : polar Q w₁ w₂ = 0 := hcorth i₀ i₁ hi
    have h21 : polar Q w₂ w₁ = 0 := hcorth i₁ i₀ hi.symm
    have hspan (w : W) : (w : V) = (c.repr w i₀) • w₁ + (c.repr w i₁) • w₂ := by
      have h := c.sum_repr w
      have huniv : (Finset.univ : Finset (Fin (Module.finrank F W))) = {i₀, i₁} := by
        ext i
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        rcases Nat.lt_or_ge i.val 1 with hlt | hge
        · exact Or.inl (Fin.ext (by simp [i₀]; omega))
        · exact Or.inr (Fin.ext (by simp [i₁]; omega))
      rw [huniv, Finset.sum_pair hi] at h
      exact (congrArg Subtype.val h).symm
    let x₁ : {x : V // Q x ≠ 0} := ⟨w₁, hcQ i₀⟩
    let x₂ : {x : V // Q x ≠ 0} := ⟨w₂, hcQ i₁⟩
    let l : List {x : V // Q x ≠ 0} := [x₁, x₂]
    have hl : Even l.length := ⟨1, rfl⟩
    have hR : ∀ v, ℓ v = reflectionWord Q l v := by
      intro v
      obtain ⟨u, hu, w, hw, rfl⟩ := hdecomp v
      obtain ⟨a, b, hab⟩ : ∃ a b : F, w = a • w₁ + b • w₂ := ⟨_, _, hspan ⟨w, hw⟩⟩
      have hu₁ := hrefl_perp u hu w₁ (c i₀).2 (hcQ i₀)
      have hu₂ := hrefl_perp u hu w₂ (c i₁).2 (hcQ i₁)
      have hs₁ := hrefl_self w₁ (hcQ i₀)
      have hs₂ := hrefl_self w₂ (hcQ i₁)
      have ho₁ := hrefl_orth w₂ w₁ (hcQ i₁) h12
      have ho₂ := hrefl_orth w₁ w₂ (hcQ i₀) h21
      change ℓ (u + w) = reflection Q w₂ (hcQ i₁) (reflection Q w₁ (hcQ i₀) (u + w))
      have hRW : reflection Q w₂ (hcQ i₁) (reflection Q w₁ (hcQ i₀) (a • w₁ + b • w₂)) =
          -(a • w₁ + b • w₂) := by
        rw [map_add (reflection Q w₁ (hcQ i₀)), map_smul, map_smul, hs₁, ho₂, map_add,
          map_smul, map_smul, map_neg, ho₁, hs₂]
        module
      rw [map_add, hu, hneg w hw, map_add (reflection Q w₁ (hcQ i₀)),
        map_add (reflection Q w₂ (hcQ i₁)), hu₁, hu₂, hab, hRW]
    -- The Clifford word of `w₁, w₂` and the unit differ by a scalar.
    let a := cliffordReflectionWord Q l
    have ha : (a : CliffordAlgebra Q) = ι Q w₂ * ι Q w₁ := by
      simp [a, l, cliffordReflectionWord, x₁, x₂]
    obtain ⟨t, -, ht⟩ := exists_smul_of_even_clifford_conj_eq Q hQ (unit Q s) a
      (involute_unit Q s) (involute_cliffordReflectionWord_of_even Q l hl) (fun v => by
        rw [unit_conj_vector, cliffordReflectionWord_conj_of_even Q l hl, ← hR v])
    have hnorm := reverse_mul_unit Q s
    have hval := reverse_mul_cliffordReflectionWord Q l
    have hl' : (l.map (fun x : {x : V // Q x ≠ 0} => Q x)).prod = Q w₁ * Q w₂ := by
      simp [l, x₁, x₂]
    rw [hl'] at hval
    rw [ht, map_smul, smul_mul_smul_comm, hval, Algebra.smul_def, ← map_mul] at hnorm
    have hanti : ι Q w₁ * ι Q w₂ = -(ι Q w₂ * ι Q w₁) := by
      rw [ι_mul_ι_comm, h12, map_zero, zero_sub]
    have hsq : (a : CliffordAlgebra Q) * a =
        -algebraMap F (CliffordAlgebra Q) (Q w₁ * Q w₂) := by
      rw [ha]
      calc ι Q w₂ * ι Q w₁ * (ι Q w₂ * ι Q w₁) = ι Q w₂ * (ι Q w₁ * ι Q w₂) * ι Q w₁ := by
            simp only [mul_assoc]
        _ = -(ι Q w₂ * ι Q w₂ * (ι Q w₁ * ι Q w₁)) := by
            rw [hanti]
            simp only [mul_neg, neg_mul, mul_assoc]
        _ = _ := by
            rw [ι_sq_scalar, ι_sq_scalar, ← map_mul, mul_comm (Q w₂)]
    rw [ht, smul_mul_smul_comm, hsq, smul_neg, Algebra.smul_def, ← map_mul, hnorm]
