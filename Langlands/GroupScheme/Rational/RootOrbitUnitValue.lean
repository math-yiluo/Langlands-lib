import Langlands.GroupScheme.Rational.RootGaloisOrbits

/-! # Galois-equivariant unit values on one actual root orbit

For a finite Galois extension `K / k` and an actual root `β` of `j_K`, every unit `c` of the
stabilizer field `rootOrbitField k K j β` extends to a Galois-equivariant function on the
actual roots: its value at `σ • β` is `σ c`, and its value off the Galois orbit of `β` is
`1`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

local instance (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

attribute [local instance] rootsGaloisAction

/-- Two Galois elements that move `β` to the same actual root agree on its stabilizer
field. -/
theorem apply_eq_of_smul_eq_of_mem_rootOrbitField
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] (j : T.toGrp ⟶ G)
    (β : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map j))
    {x : K} (hx : x ∈ rootOrbitField k K j β) {σ τ : K ≃ₐ[k] K} (h : σ • β = τ • β) :
    σ x = τ x := by
  have hst : (τ⁻¹ * σ) • β = β := by
    rw [mul_smul, h, ← mul_smul, inv_mul_cancel, one_smul]
  have hfix : (τ⁻¹ * σ) x = x :=
    (mem_rootOrbitField_iff k K j β x).mp hx (τ⁻¹ * σ) (congrArg Subtype.val hst)
  calc σ x = τ ((τ⁻¹ * σ) x) := by
        rw [AlgEquiv.mul_apply, ← AlgEquiv.mul_apply τ τ⁻¹, mul_inv_cancel, AlgEquiv.one_apply]
    _ = τ x := by rw [hfix]

/-- **Equivariant unit values on one root orbit.** Let `β` be an actual root of `j_K` and
`c` a unit of `K` lying in the stabilizer field of `β`. There is a function `ψ` from the
actual roots to `Kˣ` that is Galois-equivariant, takes the value `c` at `β`, and takes the
value `1` at every actual root outside the Galois orbit of `β`. -/
theorem exists_rootOrbitValue
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] (j : T.toGrp ⟶ G)
    (β : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map j))
    (c : Kˣ) (hc : (c : K) ∈ rootOrbitField k K j β) :
    ∃ ψ : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        (G := (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map j) → Kˣ,
      (∀ (σ : K ≃ₐ[k] K)
          (γ : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
            (G := (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
            ((GroupScheme.baseChange (algebraBaseMap k K)).map j)),
        ψ (σ • γ) = Units.map σ.toMonoidHom (ψ γ)) ∧
      ψ β = c ∧
      ∀ γ : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
          (G := (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
          ((GroupScheme.baseChange (algebraBaseMap k K)).map j),
        γ ∉ MulAction.orbit (K ≃ₐ[k] K) β → ψ γ = 1 := by
  classical
  -- the value at `γ = τ • β` is `τ c`, for any choice of `τ`
  let ψ : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map j) → Kˣ := fun γ =>
    if h : γ ∈ MulAction.orbit (K ≃ₐ[k] K) β then
      Units.map (MulAction.mem_orbit_iff.mp h).choose.toMonoidHom c
    else 1
  have hval : ∀ (τ : K ≃ₐ[k] K), ((ψ (τ • β) : Kˣ) : K) = τ (c : K) := by
    intro τ
    have h : τ • β ∈ MulAction.orbit (K ≃ₐ[k] K) β := MulAction.mem_orbit β τ
    simp only [ψ, h, ↓reduceDIte]
    exact apply_eq_of_smul_eq_of_mem_rootOrbitField k K j β hc
      ((MulAction.mem_orbit_iff.mp h).choose_spec)
  refine ⟨ψ, fun σ γ => ?_, ?_, fun γ hγ => by simp only [ψ, hγ, ↓reduceDIte]⟩
  · by_cases hγ : γ ∈ MulAction.orbit (K ≃ₐ[k] K) β
    · obtain ⟨τ, rfl⟩ := MulAction.mem_orbit_iff.mp hγ
      apply Units.ext
      rw [← mul_smul, hval, Units.coe_map, hval, AlgEquiv.mul_apply]
      rfl
    · have hσγ : σ • γ ∉ MulAction.orbit (K ≃ₐ[k] K) β := fun h => by
        obtain ⟨ρ, hρ⟩ := MulAction.mem_orbit_iff.mp h
        exact hγ (MulAction.mem_orbit_iff.mpr ⟨σ⁻¹ * ρ, by rw [mul_smul, hρ, inv_smul_smul]⟩)
      simp only [ψ, hγ, hσγ, ↓reduceDIte, map_one]
  · apply Units.ext
    have := hval 1
    rw [one_smul] at this
    rw [this, AlgEquiv.one_apply]

end Langlands.GroupScheme
