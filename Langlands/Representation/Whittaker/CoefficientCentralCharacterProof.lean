import Langlands.Representation.Whittaker.CoefficientCentralCharacterStatement

noncomputable section

namespace Langlands.Whittaker

universe uG uV

/-- The center acts through one locally constant character on every coefficient
image of a smooth representation with a one-dimensional functional space. -/
theorem coefficientCentralCharacter (G : Type uG) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    CoefficientCentralCharacterStatement.{uG, uV} G := by
  classical
  intro N θ V _ _ ρ hρ he
  obtain ⟨e⟩ := he
  let ℓ₀ : functionals N θ ρ := e.symm 1
  have hℓ₀ : ℓ₀.val ≠ 0 := by
    intro hz
    have hz' : ℓ₀ = 0 := Subtype.ext hz
    have he := congrArg e hz'
    simp [ℓ₀] at he
  have hex : ∃ v : V, ℓ₀.val v ≠ 0 := by
    by_contra h
    apply hℓ₀
    ext v
    exact not_not.mp ((not_exists.mp h) v)
  obtain ⟨v, hv⟩ := hex
  have hscale (ℓ : functionals N θ ρ) : ℓ = e ℓ • ℓ₀ := by
    apply e.injective
    simp [ℓ₀]
  let A (z : Subgroup.center G) (ℓ : functionals N θ ρ) :
      functionals N θ ρ :=
    ⟨ℓ.val.comp (ρ (z : G)), by
      intro n x
      change ℓ.val (ρ (z : G) (ρ (n : G) x)) =
        (θ n : ℂ) * ℓ.val (ρ (z : G) x)
      rw [← Module.End.mul_apply, ← map_mul,
        ← Subgroup.mem_center_iff.mp z.property (n : G),
        map_mul, Module.End.mul_apply]
      exact ℓ.property n (ρ (z : G) x)⟩
  let c (z : Subgroup.center G) : ℂ := e (A z ℓ₀)
  have act₀ (z : Subgroup.center G) (x : V) :
      ℓ₀.val (ρ (z : G) x) = c z * ℓ₀.val x :=
    congrArg (fun ℓ : functionals N θ ρ => ℓ.val x) (hscale (A z ℓ₀))
  have act (ℓ : functionals N θ ρ) (z : Subgroup.center G) (x : V) :
      ℓ.val (ρ (z : G) x) = c z * ℓ.val x := by
    have h (y : V) : ℓ.val y = e ℓ * ℓ₀.val y :=
      congrArg (fun m : functionals N θ ρ => m.val y) (hscale ℓ)
    rw [h, act₀, h]
    exact mul_left_comm _ _ _
  have c_one : c 1 = 1 := by
    apply mul_right_cancel₀ hv
    rw [← act₀]
    simp
  have c_mul (z w : Subgroup.center G) : c (z * w) = c z * c w := by
    apply mul_right_cancel₀ hv
    rw [← act₀]
    change ℓ₀.val (ρ ((z : G) * (w : G)) v) = _
    rw [map_mul, Module.End.mul_apply, act₀, act₀, mul_assoc]
  have c_ne (z : Subgroup.center G) : c z ≠ 0 := by
    intro hz
    have h := c_mul z⁻¹ z
    rw [inv_mul_cancel, c_one, hz, mul_zero] at h
    exact one_ne_zero h
  let χ : Subgroup.center G →* ℂˣ :=
    { toFun := fun z => Units.mk0 (c z) (c_ne z)
      map_one' := Units.ext c_one
      map_mul' := fun z w => Units.ext (c_mul z w) }
  have hχ (ℓ : functionals N θ ρ) (z : Subgroup.center G) (x : V) :
      ℓ.val (ρ (z : G) x) = (χ z : ℂ) * ℓ.val x := act ℓ z x
  have hlc : IsLocallyConstant (χ : Subgroup.center G → ℂˣ) := by
    obtain ⟨K, hK⟩ := hρ v
    apply (IsLocallyConstant.iff_exists_open _).2
    intro z
    refine ⟨{w | (z : G)⁻¹ * (w : G) ∈ K},
      K.isOpen.preimage (continuous_const.mul continuous_subtype_val), ?_, ?_⟩
    · simp
    · intro w hw
      apply Units.ext
      apply mul_right_cancel₀ hv
      rw [← hχ, ← hχ]
      congr 1
      calc
        ρ (w : G) v = ρ (z : G) (ρ ((z : G)⁻¹ * (w : G)) v) := by
          rw [← Module.End.mul_apply, ← map_mul]
          simp
        _ = ρ (z : G) v := congrArg (ρ (z : G)) (hK ⟨_, hw⟩)
  refine ⟨χ, ⟨hlc, ?_⟩, ?_⟩
  · intro ℓ f z g
    obtain ⟨x, rfl⟩ := modelMap_surjective ρ ℓ f
    change ℓ.val (ρ ((z : G) * g) x) = (χ z : ℂ) * ℓ.val (ρ g x)
    rw [map_mul, Module.End.mul_apply, hχ]
  · intro ψ hψ
    ext z
    apply mul_right_cancel₀ hv
    have h := hψ.2 ℓ₀ (modelMap ρ ℓ₀ v) z 1
    change ℓ₀.val (ρ ((z : G) * 1) v) =
      (ψ z : ℂ) * ℓ₀.val (ρ 1 v) at h
    simpa only [mul_one, map_one, Module.End.one_apply, hχ] using h.symm

end Langlands.Whittaker
