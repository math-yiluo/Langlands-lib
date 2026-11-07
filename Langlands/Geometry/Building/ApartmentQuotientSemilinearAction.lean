import Langlands.Geometry.Building.ApartmentQuotient

/-! # Semilinear actions on the existing apartment quotient -/

namespace Langlands.Geometry.Building.ApartmentQuotient

universe uH uA uΓ

variable {H : Type uH} [Group H] {N : Subgroup H}
  {A : Type uA} [MulAction N A] (P : CovariantSubgroupFamily N A)
  {Γ : Type uΓ} [Group Γ] (ρ : Γ →* MulAut H)

/-- Apartment data that let a group of automorphisms of `H` act on the
existing quotient. Normalizer and subgroup compatibility are explicit. -/
structure SemilinearActionData where
  /-- The action on the original apartment. -/
  apartment : Γ →* Equiv.Perm A
  /-- The group automorphisms preserve the original normalizer. -/
  normalizer_mem : ∀ (σ : Γ) (n : N), ρ σ (n : H) ∈ N
  /-- The apartment action intertwines the actual normalizer actions. -/
  normalizer_smul : ∀ (σ : Γ) (n : N) (x : A),
    apartment σ (n • x) = (⟨ρ σ (n : H), normalizer_mem σ n⟩ : N) • apartment σ x
  /-- The automorphisms preserve the subgroup attached to every point. -/
  subgroup_mem : ∀ (σ : Γ) (x : A) (p : H), p ∈ P x → ρ σ p ∈ P (apartment σ x)

namespace SemilinearActionData

variable {P ρ} (D : SemilinearActionData P ρ)

/-- The action on representatives respects the exact original quotient relation. -/
theorem apartmentRel_map (σ : Γ) {a b : H × A}
    (hab : apartmentRel N P a b) :
    apartmentRel N P (ρ σ a.1, D.apartment σ a.2)
      (ρ σ b.1, D.apartment σ b.2) := by
  obtain ⟨n, hn, hp⟩ := hab
  refine ⟨⟨ρ σ (n : H), D.normalizer_mem σ n⟩, ?_, ?_⟩
  · rw [← D.normalizer_smul, hn]
  · have h := D.subgroup_mem σ a.2 _ hp
    simpa only [map_mul, map_inv] using h

/-- Descend both the group and apartment actions to the existing quotient. -/
def map (σ : Γ) : ApartmentQuotient P → ApartmentQuotient P :=
  Quotient.map' (fun a : H × A => (ρ σ a.1, D.apartment σ a.2))
    (fun _ _ hab => D.apartmentRel_map σ hab)

@[simp] theorem map_mk (σ : Γ) (g : H) (x : A) :
    D.map σ (ApartmentQuotient.mk P (g, x)) = ApartmentQuotient.mk P (ρ σ g, D.apartment σ x) := rfl

@[simp] theorem map_apartment (σ : Γ) (x : A) :
    D.map σ (ApartmentQuotient.apartment P x) =
      ApartmentQuotient.apartment P (D.apartment σ x) := by
  change ApartmentQuotient.mk P (ρ σ 1, D.apartment σ x) = ApartmentQuotient.mk P (1, D.apartment σ x)
  rw [_root_.map_one]

theorem map_one (q : ApartmentQuotient P) : D.map 1 q = q := by
  induction q using ind with
  | h g x =>
    change ApartmentQuotient.mk P ((ρ 1) g, (D.apartment 1) x) = ApartmentQuotient.mk P (g, x)
    simp only [_root_.map_one, MulAut.one_apply, Equiv.Perm.one_apply]

theorem map_mul (σ τ : Γ) (q : ApartmentQuotient P) :
    D.map (σ * τ) q = D.map σ (D.map τ q) := by
  induction q using ind with
  | h g x =>
    change ApartmentQuotient.mk P ((ρ (σ * τ)) g, (D.apartment (σ * τ)) x) =
      ApartmentQuotient.mk P ((ρ σ) ((ρ τ) g), (D.apartment σ) ((D.apartment τ) x))
    simp only [_root_.map_mul, MulAut.mul_apply, Equiv.Perm.mul_apply]

/-- The resulting action is semilinear for the original `H`-action. -/
theorem map_smul (σ : Γ) (g : H) (q : ApartmentQuotient P) :
    D.map σ (g • q) = ρ σ g • D.map σ q := by
  induction q using ind with
  | h h x =>
    change ApartmentQuotient.mk P (ρ σ (g * h), D.apartment σ x) =
      ApartmentQuotient.mk P (ρ σ g * ρ σ h, D.apartment σ x)
    rw [_root_.map_mul]

/-- A genuine group action by permutations of the existing quotient,
with the actual original group action intertwined by `ρ`. -/
def action : Γ →* Equiv.Perm (ApartmentQuotient P) where
  toFun σ :=
    { toFun := D.map σ
      invFun := D.map σ⁻¹
      left_inv q := by rw [← D.map_mul, inv_mul_cancel, D.map_one]
      right_inv q := by rw [← D.map_mul, mul_inv_cancel, D.map_one] }
  map_one' := Equiv.ext D.map_one
  map_mul' σ τ := Equiv.ext (D.map_mul σ τ)

@[simp] theorem action_apply (σ : Γ) (q : ApartmentQuotient P) :
    D.action σ q = D.map σ q := rfl

@[simp] theorem action_mk (σ : Γ) (g : H) (x : A) :
    D.action σ (ApartmentQuotient.mk P (g, x)) = ApartmentQuotient.mk P (ρ σ g, D.apartment σ x) := rfl

@[simp] theorem action_apartment (σ : Γ) (x : A) :
    D.action σ (ApartmentQuotient.apartment P x) =
      ApartmentQuotient.apartment P (D.apartment σ x) :=
  D.map_apartment σ x

theorem action_smul (σ : Γ) (g : H) (q : ApartmentQuotient P) :
    D.action σ (g • q) = ρ σ g • D.action σ q :=
  D.map_smul σ g q

/-- Full point fixation is preserved and reflected through the same group
automorphism and the constructed quotient permutation. -/
theorem action_smul_eq_iff (σ : Γ) (g : H) (q : ApartmentQuotient P) :
    ρ σ g • D.action σ q = D.action σ q ↔ g • q = q := by
  rw [← D.action_smul]
  exact (D.action σ).injective.eq_iff

end SemilinearActionData

end Langlands.Geometry.Building.ApartmentQuotient
