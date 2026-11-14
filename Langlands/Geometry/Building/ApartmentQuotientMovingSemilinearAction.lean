import Langlands.Geometry.Building.ApartmentQuotientSemilinearAction
import Langlands.Geometry.Building.ApartmentQuotientComparison
import Mathlib.Topology.MetricSpace.IsometricSMul

/-! # Semilinear quotient actions with a moving reference apartment -/

namespace Langlands.Geometry.Building.ApartmentQuotient

universe uH uA uΓ

variable {H : Type uH} [Group H] {N : Subgroup H}
  {A : Type uA} [MulAction N A] (P : CovariantSubgroupFamily N A)
  {Γ : Type uΓ} [Group Γ] (ρ : Γ →* MulAut H)

/-- Corrected apartment maps need only compose up to the original normalizer.
The corrections permit coefficient automorphisms to move the reference torus. -/
structure MovingSemilinearActionData where
  /-- The group element that returns an image apartment to the chosen apartment. -/
  correction : Γ → H
  /-- The resulting maps on the chosen apartment, before quotienting. -/
  apartment : Γ → A → A
  /-- The corrected coefficient automorphism preserves the normalizer. -/
  normalizer_mem : ∀ (σ : Γ) (n : N),
    (correction σ)⁻¹ * ρ σ (n : H) * correction σ ∈ N
  /-- Corrected apartment maps intertwine the original normalizer action. -/
  normalizer_smul : ∀ (σ : Γ) (n : N) (x : A),
    apartment σ (n • x) =
      (⟨(correction σ)⁻¹ * ρ σ (n : H) * correction σ,
        normalizer_mem σ n⟩ : N) • apartment σ x
  /-- Corrected coefficient transport preserves the attached subgroups. -/
  subgroup_mem : ∀ (σ : Γ) (x : A) (p : H), p ∈ P x →
    (correction σ)⁻¹ * ρ σ p * correction σ ∈ P (apartment σ x)
  /-- Normalize the correction for the identity coefficient automorphism. -/
  correction_one : correction 1 = 1
  /-- Normalize the apartment map for the identity coefficient automorphism. -/
  apartment_one : ∀ x : A, apartment 1 x = x
  /-- The difference between chosen corrections for a composite and its factors. -/
  defect : Γ → Γ → N
  /-- The correction composition law holds up to this normalizer element. -/
  correction_mul : ∀ σ τ : Γ,
    correction (σ * τ) * (defect σ τ : H) = ρ σ (correction τ) * correction σ
  /-- The same defect accounts for composition of the apartment maps. -/
  apartment_mul : ∀ (σ τ : Γ) (x : A),
    apartment (σ * τ) x = defect σ τ • apartment σ (apartment τ x)

namespace MovingSemilinearActionData

variable {P ρ} (D : MovingSemilinearActionData P ρ)

/-- The corrected maps preserve the exact original quotient relation. -/
theorem apartmentRel_map (σ : Γ) {a b : H × A}
    (hab : apartmentRel N P a b) :
    apartmentRel N P (ρ σ a.1 * D.correction σ, D.apartment σ a.2)
      (ρ σ b.1 * D.correction σ, D.apartment σ b.2) := by
  obtain ⟨n, hn, hp⟩ := hab
  refine ⟨⟨_, D.normalizer_mem σ n⟩, ?_, ?_⟩
  · rw [← D.normalizer_smul, hn]
  · have h := D.subgroup_mem σ a.2 _ hp
    simpa only [map_mul, map_inv, mul_inv_rev, mul_assoc,
      mul_inv_cancel_left, inv_mul_cancel_left] using h

/-- Descend the corrected representative maps to the original quotient. -/
def map (σ : Γ) : ApartmentQuotient P → ApartmentQuotient P :=
  Quotient.map' (fun a : H × A => (ρ σ a.1 * D.correction σ, D.apartment σ a.2))
    (fun _ _ hab => D.apartmentRel_map σ hab)

@[simp] theorem map_mk (σ : Γ) (g : H) (x : A) :
    D.map σ (ApartmentQuotient.mk P (g, x)) = ApartmentQuotient.mk P (ρ σ g * D.correction σ, D.apartment σ x) := rfl

@[simp] theorem map_apartment (σ : Γ) (x : A) :
    D.map σ (ApartmentQuotient.apartment P x) =
      D.correction σ • ApartmentQuotient.apartment P (D.apartment σ x) := by
  rw [ApartmentQuotient.apartment, map_mk, _root_.map_one, one_mul,
    mk_eq_smul_apartment]

theorem map_one (q : ApartmentQuotient P) : D.map 1 q = q := by
  induction q using ind with
  | h g x =>
    rw [map_mk, _root_.map_one, MulAut.one_apply, D.correction_one,
      D.apartment_one, mul_one]

/-- Normalizer defects disappear in the original quotient relation. -/
theorem map_mul (σ τ : Γ) (q : ApartmentQuotient P) :
    D.map (σ * τ) q = D.map σ (D.map τ q) := by
  induction q using ind with
  | h g x =>
    rw [map_mk, map_mk, map_mk, _root_.map_mul, MulAut.mul_apply,
      _root_.map_mul, D.apartment_mul]
    apply (mk_eq_mk_iff P _ _ _ _).2
    refine ⟨(D.defect σ τ)⁻¹, inv_smul_smul _ _, ?_⟩
    have he :
        ((ρ σ ((ρ τ) g) * D.correction (σ * τ))⁻¹ *
          (ρ σ ((ρ τ) g) * ρ σ (D.correction τ) * D.correction σ)) *
            ((D.defect σ τ : H)⁻¹) = 1 := by
      calc
        _ = (D.correction (σ * τ))⁻¹ *
            (ρ σ (D.correction τ) * D.correction σ) *
              ((D.defect σ τ : H)⁻¹) := by simp [mul_inv_rev, mul_assoc]
        _ = 1 := by rw [← D.correction_mul]; simp
    change _ * ((D.defect σ τ : H)⁻¹) ∈ _
    rw [he]
    exact (P _).one_mem

/-- The corrected action is semilinear for the existing group action. -/
theorem map_smul (σ : Γ) (g : H) (q : ApartmentQuotient P) :
    D.map σ (g • q) = ρ σ g • D.map σ q := by
  induction q using ind with
  | h h x =>
    rw [smul_mk, map_mk, map_mk, smul_mk, _root_.map_mul, mul_assoc]

/-- A coherent homomorphism on the quotient, although its chosen apartment maps
are only coherent up to normalizer defects. -/
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
    D.action σ (ApartmentQuotient.mk P (g, x)) = ApartmentQuotient.mk P (ρ σ g * D.correction σ, D.apartment σ x) := rfl

@[simp] theorem action_apartment (σ : Γ) (x : A) :
    D.action σ (ApartmentQuotient.apartment P x) =
      D.correction σ • ApartmentQuotient.apartment P (D.apartment σ x) :=
  D.map_apartment σ x

theorem action_smul (σ : Γ) (g : H) (q : ApartmentQuotient P) :
    D.action σ (g • q) = ρ σ g • D.action σ q := D.map_smul σ g q

/-- Full point fixation is transported and reflected by the same coefficient
automorphism and quotient permutation. -/
theorem action_smul_eq_iff (σ : Γ) (g : H) (q : ApartmentQuotient P) :
    ρ σ g • D.action σ q = D.action σ q ↔ g • q = q := by
  rw [← D.action_smul]
  exact (D.action σ).injective.eq_iff

/-- Altering a correction by a normalizer element, and compensating on the
apartment by its inverse, leaves the quotient map unchanged. -/
theorem map_eq_of_normalizer (D' : MovingSemilinearActionData P ρ) (σ : Γ) (n : N)
    (hc : D'.correction σ = D.correction σ * (n : H))
    (ha : ∀ x : A, D.apartment σ x = n • D'.apartment σ x) :
    D.map σ = D'.map σ := by
  funext q
  induction q using ind with
  | h g x =>
    rw [map_mk, map_mk, hc, ha, mk_eq_smul_apartment, mk_eq_smul_apartment,
      apartment_smul, smul_smul, mul_assoc]

/-- The entire homomorphism is independent of such simultaneous changes of
normalizer corrections. -/
theorem action_eq_of_normalizer (D' : MovingSemilinearActionData P ρ) (n : Γ → N)
    (hc : ∀ σ, D'.correction σ = D.correction σ * (n σ : H))
    (ha : ∀ σ x, D.apartment σ x = n σ • D'.apartment σ x) :
    D.action = D'.action := by
  ext σ q
  exact congrFun (D.map_eq_of_normalizer D' σ (n σ) (hc σ) (ha σ)) q

/-- When any two points share a translated apartment, a coefficient map is an
isometry as soon as its corrected apartment map preserves the chart distances.
The same metric and the original scalar action are used throughout. -/
theorem action_isometry [PseudoMetricSpace (ApartmentQuotient P)]
    [IsIsometricSMul H (ApartmentQuotient P)]
    (hcommon : HasCommonTranslatedApartment P)
    (hapt : ∀ (σ : Γ) (x y : A),
      dist (ApartmentQuotient.apartment P (D.apartment σ x))
          (ApartmentQuotient.apartment P (D.apartment σ y)) =
        dist (ApartmentQuotient.apartment P x) (ApartmentQuotient.apartment P y))
    (σ : Γ) : Isometry (D.action σ) := by
  refine Isometry.of_dist_eq fun q q' => ?_
  obtain ⟨g, x, y, rfl, rfl⟩ := hcommon q q'
  rw [D.action_smul, D.action_smul, D.action_apartment, D.action_apartment,
    dist_smul, dist_smul, hapt, dist_smul]

end MovingSemilinearActionData

end Langlands.Geometry.Building.ApartmentQuotient
