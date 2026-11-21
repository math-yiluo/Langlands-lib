import Langlands.BushnellKutzko.CharacterIntertwining

/-! # Intertwining of representations of subgroups (BK93 §4.1, p. 144; (5.1.7), p. 160) -/

noncomputable section

namespace Langlands.BushnellKutzko

universe uG uW uW₁ uW₂

variable {G : Type uG} [Group G]

/-- The group `x⁻¹K₁x ∩ K₂`, written as the elements `h ∈ K₂` with `x h x⁻¹ ∈ K₁`. -/
def intertwiningDomain (K₁ K₂ : Subgroup G) (x : G) : Subgroup G :=
  K₁.comap (MulAut.conj x).toMonoidHom ⊓ K₂

theorem mem_intertwiningDomain {K₁ K₂ : Subgroup G} {x h : G} :
    h ∈ intertwiningDomain K₁ K₂ x ↔ x * h * x⁻¹ ∈ K₁ ∧ h ∈ K₂ :=
  Iff.rfl

/-- The map `h ↦ x h x⁻¹` from `x⁻¹K₁x ∩ K₂` to `K₁`. -/
def intertwiningDomainConj (K₁ K₂ : Subgroup G) (x : G) : intertwiningDomain K₁ K₂ x →* K₁ :=
  ((MulAut.conj x).toMonoidHom.comp (intertwiningDomain K₁ K₂ x).subtype).codRestrict K₁
    (fun h => h.2.1)

@[simp] theorem coe_intertwiningDomainConj (K₁ K₂ : Subgroup G) (x : G)
    (h : intertwiningDomain K₁ K₂ x) :
    (intertwiningDomainConj K₁ K₂ x h : G) = x * h * x⁻¹ :=
  rfl

/-- The inclusion of `x⁻¹K₁x ∩ K₂` in `K₂`. -/
def intertwiningDomainIncl (K₁ K₂ : Subgroup G) (x : G) : intertwiningDomain K₁ K₂ x →* K₂ :=
  Subgroup.inclusion inf_le_right

@[simp] theorem coe_intertwiningDomainIncl (K₁ K₂ : Subgroup G) (x : G)
    (h : intertwiningDomain K₁ K₂ x) :
    (intertwiningDomainIncl K₁ K₂ x h : G) = h :=
  rfl

variable {K₁ K₂ : Subgroup G} {W₁ : Type uW₁} {W₂ : Type uW₂}
  [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]

/-- The space `I_x(ρ₁, ρ₂)` of `x⁻¹K₁x ∩ K₂`-homomorphisms from `ρ₁^x : h ↦ ρ₁(x h x⁻¹)` to
`ρ₂`. -/
abbrev intertwiningSpace (ρ₁ : Representation ℂ K₁ W₁) (ρ₂ : Representation ℂ K₂ W₂) (x : G) :=
  Representation.IntertwiningMap (ρ₁.comp (intertwiningDomainConj K₁ K₂ x))
    (ρ₂.comp (intertwiningDomainIncl K₁ K₂ x))

/-- `x` intertwines `ρ₁` with `ρ₂` when `I_x(ρ₁, ρ₂)` is nonzero. -/
def Intertwines (ρ₁ : Representation ℂ K₁ W₁) (ρ₂ : Representation ℂ K₂ W₂) (x : G) : Prop :=
  ∃ f : intertwiningSpace ρ₁ ρ₂ x, f ≠ 0

/-- The intertwining set `I_G(ρ₁, ρ₂)`. -/
def representationIntertwining (ρ₁ : Representation ℂ K₁ W₁) (ρ₂ : Representation ℂ K₂ W₂) :
    Set G :=
  {x | Intertwines ρ₁ ρ₂ x}

/-- The self-intertwining set `I_G(ρ) = I_G(ρ, ρ)`. -/
abbrev representationSelfIntertwining (ρ : Representation ℂ K₁ W₁) : Set G :=
  representationIntertwining ρ ρ

/-- The representation of `H` on `ℂ` attached to a character `χ : H → ℂˣ`. -/
def characterRepresentation {H : Subgroup G} (χ : H →* ℂˣ) : Representation ℂ H ℂ where
  toFun h := (χ h : ℂ) • LinearMap.id
  map_one' := by
    ext
    simp
  map_mul' a b := by
    ext
    simp [mul_comm]

@[simp] theorem characterRepresentation_apply {H : Subgroup G} (χ : H →* ℂˣ) (h : H) (z : ℂ) :
    characterRepresentation χ h z = (χ h : ℂ) * z :=
  rfl

/-- For characters, `representationIntertwining` agrees with Task 7422's
`characterIntertwining`. -/
theorem mem_representationIntertwining_characterRepresentation_iff {H₁ H₂ : Subgroup G}
    (χ₁ : H₁ →* ℂˣ) (χ₂ : H₂ →* ℂˣ) (x : G) :
    x ∈ representationIntertwining (characterRepresentation χ₁) (characterRepresentation χ₂) ↔
      x ∈ characterIntertwining χ₁ χ₂ := by
  constructor
  · rintro ⟨f, hf⟩ h hh
    have hf1 : f 1 ≠ 0 := by
      intro h0
      apply hf
      apply Representation.IntertwiningMap.ext
      refine LinearMap.ext fun z => ?_
      have hz : f z = z * f 1 := by
        simpa using f.toLinearMap.map_smul z 1
      show f z = 0
      rw [hz, h0, mul_zero]
    set d : intertwiningDomain H₁ H₂ x := ⟨(h : G), hh, h.2⟩
    have key := Representation.IntertwiningMap.isIntertwining _ _ f d 1
    have hlin : ∀ c : ℂ, f c = c * f 1 := fun c => by
      simpa using f.toLinearMap.map_smul c 1
    simp only [MonoidHom.coe_comp, Function.comp_apply, characterRepresentation_apply,
      mul_one] at key
    rw [hlin] at key
    have hk : ((χ₁ (intertwiningDomainConj H₁ H₂ x d) : ℂˣ) : ℂ) =
        ((χ₂ (intertwiningDomainIncl H₁ H₂ x d) : ℂˣ) : ℂ) :=
      mul_right_cancel₀ hf1 key
    exact Units.ext hk
  · intro hx
    refine ⟨⟨LinearMap.id, fun d => ?_⟩, ?_⟩
    · ext
      have := hx (intertwiningDomainIncl H₁ H₂ x d) d.2.1
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
        MonoidHom.coe_comp, characterRepresentation_apply, mul_one]
      exact congrArg Units.val this
    · intro h0
      have := congrArg (fun f : intertwiningSpace (characterRepresentation χ₁)
        (characterRepresentation χ₂) x => f 1) h0
      simp at this

end Langlands.BushnellKutzko
