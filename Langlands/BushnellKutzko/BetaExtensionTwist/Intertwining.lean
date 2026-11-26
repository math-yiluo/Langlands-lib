import Langlands.BushnellKutzko.BetaExtensionTwist.Algebra
import Langlands.BushnellKutzko.RepresentationIntertwining

/-! # Restriction and transport of intertwining for a beta-extension twist -/

noncomputable section
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uG uM uN uW

variable {G : Type uG} [Group G] {J K U : Subgroup G}
  {M : Type uM} [AddCommGroup M] [Module ℂ M]
  {N : Type uN} [AddCommGroup N] [Module ℂ N]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

section Transport

private theorem intertwiningDomain_mono (h : K ≤ J) (y : G) :
    intertwiningDomain K K y ≤ intertwiningDomain J J y :=
  fun _ hx => ⟨h hx.1, h hx.2⟩

private abbrev domainInclusion (h : K ≤ J) (y : G) :=
  Subgroup.inclusion (intertwiningDomain_mono h y)

/-- Restriction of an intertwiner to the intersection attached to a smaller subgroup. -/
def intertwiningSpaceRestrict (h : K ≤ J) (ρ : Representation ℂ J M) (y : G) :
    intertwiningSpace ρ ρ y →ₗ[ℂ]
      intertwiningSpace (ρ.comp (Subgroup.inclusion h)) (ρ.comp (Subgroup.inclusion h)) y where
  toFun f := ⟨f.toLinearMap, fun d => f.isIntertwining' (domainInclusion h y d)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Transporting a representation equivalence through both restriction maps of the domain. -/
def intertwiningSpaceCongr {ρ : Representation ℂ J M} {σ : Representation ℂ J W}
    (e : Representation.Equiv ρ σ) (y : G) :
    intertwiningSpace ρ ρ y ≃ₗ[ℂ] intertwiningSpace σ σ y := by
  let e₁ : Representation.Equiv (ρ.comp (intertwiningDomainConj J J y))
      (σ.comp (intertwiningDomainConj J J y)) :=
    Representation.Equiv.mk e.toLinearEquiv (fun d => e.isIntertwining' (intertwiningDomainConj J J y d))
  let e₂ : Representation.Equiv (ρ.comp (intertwiningDomainIncl J J y))
      (σ.comp (intertwiningDomainIncl J J y)) :=
    Representation.Equiv.mk e.toLinearEquiv (fun d => e.isIntertwining' (intertwiningDomainIncl J J y d))
  exact
    { toFun := fun f => e₂.toIntertwiningMap.comp (f.comp e₁.symm.toIntertwiningMap)
      invFun := fun f => e₂.symm.toIntertwiningMap.comp (f.comp e₁.toIntertwiningMap)
      map_add' := by intro f g; ext v; simp
      map_smul' := by intro c f; ext v; simp
      left_inv := by intro f; ext v; simp
      right_inv := by intro f; ext v; simp }

private theorem intertwines_mul_left_right (ρ : Representation ℂ J M) {y : G}
    (a b : J) (hy : Intertwines ρ ρ y) : Intertwines ρ ρ ((a : G) * y * b) := by
  obtain ⟨f, hf⟩ := hy
  let x : G := (a : G) * y * b
  let T : Module.End ℂ M := ρ b⁻¹ ∘ₗ f.toLinearMap ∘ₗ ρ a⁻¹
  have hT (d : intertwiningDomain J J x) :
      T ∘ₗ ρ (intertwiningDomainConj J J x d) =
        ρ (intertwiningDomainIncl J J x d) ∘ₗ T := by
    let k : intertwiningDomain J J y :=
      ⟨(b : G) * (d : G) * (b : G)⁻¹, by
        have hk : y * ((b : G) * (d : G) * (b : G)⁻¹) * y⁻¹ =
            (a : G)⁻¹ * (x * (d : G) * x⁻¹) * (a : G) := by
          unfold x
          group
        change y * ((b : G) * (d : G) * (b : G)⁻¹) * y⁻¹ ∈ J
        rw [hk]
        exact J.mul_mem (J.mul_mem (J.inv_mem a.property) d.property.1) a.property,
        J.mul_mem (J.mul_mem b.property d.property.2) (J.inv_mem b.property)⟩
    have hc : a⁻¹ * intertwiningDomainConj J J x d =
        intertwiningDomainConj J J y k * a⁻¹ := by
      apply Subtype.ext
      change (a : G)⁻¹ * (x * (d : G) * x⁻¹) =
        (y * ((b : G) * (d : G) * (b : G)⁻¹) * y⁻¹) * (a : G)⁻¹
      unfold x
      group
    have hi : b⁻¹ * intertwiningDomainIncl J J y k =
        intertwiningDomainIncl J J x d * b⁻¹ := by
      apply Subtype.ext
      change (b : G)⁻¹ * ((b : G) * (d : G) * (b : G)⁻¹) = (d : G) * (b : G)⁻¹
      group
    have hc' := congrArg ρ hc
    have hi' := congrArg ρ hi
    simp only [map_mul, Module.End.mul_eq_comp] at hc' hi'
    have hF : f.toLinearMap ∘ₗ ρ (intertwiningDomainConj J J y k) =
        ρ (intertwiningDomainIncl J J y k) ∘ₗ f.toLinearMap := f.isIntertwining' k
    apply LinearMap.ext
    intro v
    simp only [T, LinearMap.comp_apply]
    have hcV := congrArg (fun q : Module.End ℂ M => q v) hc'
    have hFv := congrArg (fun q : Module.End ℂ M => q (ρ a⁻¹ v)) hF
    have hiV := congrArg (fun q : Module.End ℂ M => q (f.toLinearMap (ρ a⁻¹ v))) hi'
    simp only [LinearMap.comp_apply] at hcV hFv hiV
    rw [hcV, hFv, hiV]
  let F : intertwiningSpace ρ ρ x := ⟨T, hT⟩
  refine ⟨F, ?_⟩
  intro hF
  apply hf
  apply Representation.IntertwiningMap.ext
  ext v
  obtain ⟨w, hw⟩ := (Representation.apply_bijective ρ a⁻¹).surjective v
  have hzero := congrArg (fun q : intertwiningSpace ρ ρ x => q w) hF
  change ρ b⁻¹ (f (ρ a⁻¹ w)) = 0 at hzero
  rw [hw] at hzero
  change f v = 0
  exact (Representation.apply_bijective ρ b⁻¹).injective (by simpa only [map_zero] using hzero)

/-- Intertwining is constant on the double cosets of the representation subgroup. -/
theorem intertwines_mul_left_right_iff (ρ : Representation ℂ J M) (y : G) (a b : J) :
    Intertwines ρ ρ ((a : G) * y * b) ↔ Intertwines ρ ρ y := by
  refine ⟨fun h => ?_, intertwines_mul_left_right ρ a b⟩
  have hh := intertwines_mul_left_right ρ a⁻¹ b⁻¹ h
  change Intertwines ρ ρ ((a : G)⁻¹ * ((a : G) * y * b) * (b : G)⁻¹) at hh
  have hx : (a : G)⁻¹ * ((a : G) * y * b) * (b : G)⁻¹ = y := by group
  rwa [hx] at hh

/-- When the intersection factors through a subgroup and a group acting trivially,
restriction reflects intertwining. -/
theorem intertwines_restrict_iff_of_domain_product (hK : K ≤ J) (hU : U ≤ J)
    (ξ : Representation ℂ J N) (ht : ∀ j : J, (j : G) ∈ K → ξ j = 1) (y : G)
    (hD : ∀ d : intertwiningDomain J J y,
      ∃ u : intertwiningDomain U U y, ∃ k : intertwiningDomain K K y,
        (u : G) * (k : G) = (d : G)) :
    Intertwines (ξ.comp (Subgroup.inclusion hU)) (ξ.comp (Subgroup.inclusion hU)) y ↔
      Intertwines ξ ξ y := by
  constructor
  · rintro ⟨f, hf⟩
    have hF (d : intertwiningDomain J J y) :
        f.toLinearMap ∘ₗ ξ (intertwiningDomainConj J J y d) =
          ξ (intertwiningDomainIncl J J y d) ∘ₗ f.toLinearMap := by
      obtain ⟨u, k, h⟩ := hD d
      have heq : d = domainInclusion hU y u * domainInclusion hK y k := Subtype.ext h.symm
      rw [heq, map_mul, map_mul, map_mul, map_mul]
      rw [ht (intertwiningDomainConj J J y (domainInclusion hK y k)) k.property.1,
        ht (intertwiningDomainIncl J J y (domainInclusion hK y k)) k.property.2,
        mul_one, mul_one]
      exact f.isIntertwining' u
    refine ⟨⟨f.toLinearMap, hF⟩, ?_⟩
    intro hzero
    apply hf
    apply Representation.IntertwiningMap.ext
    exact congrArg (fun q : intertwiningSpace ξ ξ y => q.toLinearMap) hzero
  · rintro ⟨f, hf⟩
    refine ⟨intertwiningSpaceRestrict hU ξ y f, ?_⟩
    intro hzero
    apply hf
    apply Representation.IntertwiningMap.ext
    exact congrArg (fun q : intertwiningSpace (ξ.comp (Subgroup.inclusion hU))
      (ξ.comp (Subgroup.inclusion hU)) y => q.toLinearMap) hzero

end Transport

section Twist

variable (hK : K ≤ J) (κ : Representation ℂ J M) (ξ : Representation ℂ J N)
  (ht : ∀ j : J, (j : G) ∈ K → ξ j = 1)

local notation "κK" => κ.comp (Subgroup.inclusion hK)

include ht in
/-- Restricting a tensor-product intertwiner to the subgroup on which `ξ` is trivial
produces an intertwiner of the restricted `κ`. -/
theorem intertwines_restriction_of_tprod (y : G) :
    Intertwines (κ.tprod ξ) (κ.tprod ξ) y → Intertwines κK κK y := by
  rintro ⟨f, hf⟩
  exact exists_intertwiner_of_tensor_restriction (domainInclusion hK y)
    (κ.comp (intertwiningDomainConj J J y)) (κ.comp (intertwiningDomainIncl J J y))
    (ξ.comp (intertwiningDomainConj J J y)) (ξ.comp (intertwiningDomainIncl J J y))
    (fun d => ht (intertwiningDomainConj J J y (domainInclusion hK y d)) d.property.1)
    (fun d => ht (intertwiningDomainIncl J J y (domainInclusion hK y d)) d.property.2) f hf

/-- The tensor map is an equivalence if the restricted left intertwiner space has
at most dimension one and the left representation intertwines on the full domain. -/
def intertwiningSpaceTprodEquiv [FiniteDimensional ℂ M] (y : G)
    (s : intertwiningSpace κ κ y) (hs : s ≠ 0)
    (hline : Module.finrank ℂ (intertwiningSpace κK κK y) ≤ 1) :
    intertwiningSpace ξ ξ y ≃ₗ[ℂ] intertwiningSpace (κ.tprod ξ) (κ.tprod ξ) y := by
  apply tensorIntertwiningEquiv (domainInclusion hK y) _ _ _ _
    (fun d => ht (intertwiningDomainConj J J y (domainInclusion hK y d)) d.property.1)
    (fun d => ht (intertwiningDomainIncl J J y (domainInclusion hK y d)) d.property.2) s hs
  intro q
  let sK := intertwiningSpaceRestrict hK κ y s
  have hsK : sK ≠ 0 := by
    intro h
    apply hs
    apply Representation.IntertwiningMap.ext
    exact congrArg (fun q : intertwiningSpace κK κK y => q.toLinearMap) h
  have : Nontrivial (intertwiningSpace κK κK y) := ⟨⟨sK, 0, hsK⟩⟩
  have hdim := le_antisymm hline (Module.finrank_pos (R := ℂ) (M := intertwiningSpace κK κK y))
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' sK hsK).mp hdim q
  exact ⟨c, congrArg Representation.IntertwiningMap.toLinearMap hc.symm⟩

include ht in
/-- The tensor twist has the claimed support and dimension under the
intertwining inputs and the product formula for the common domain. -/
theorem tprod_intertwining_of_restriction [FiniteDimensional ℂ M]
    [FiniteDimensional ℂ N] (hU : U ≤ J) (B : Set G)
    (hsupport : representationSelfIntertwining κK ⊆ (K : Set G) * B * (K : Set G))
    (hκB : B ⊆ representationSelfIntertwining κ)
    (hline : ∀ y ∈ B, Module.finrank ℂ (intertwiningSpace κK κK y) ≤ 1)
    (hD : ∀ y ∈ B, ∀ d : intertwiningDomain J J y,
      ∃ u : intertwiningDomain U U y, ∃ k : intertwiningDomain K K y,
        (u : G) * (k : G) = (d : G)) :
    representationSelfIntertwining (κ.tprod ξ) =
      (J : Set G) * (B ∩ representationSelfIntertwining (ξ.comp (Subgroup.inclusion hU))) *
        (J : Set G) ∧
      (∀ y ∈ B, Module.finrank ℂ (intertwiningSpace (κ.tprod ξ) (κ.tprod ξ) y) =
        Module.finrank ℂ (intertwiningSpace ξ ξ y)) := by
  have E (y : G) (hy : y ∈ B) : Nonempty
      (intertwiningSpace ξ ξ y ≃ₗ[ℂ] intertwiningSpace (κ.tprod ξ) (κ.tprod ξ) y) := by
    obtain ⟨s, hs⟩ := hκB hy
    exact ⟨intertwiningSpaceTprodEquiv hK κ ξ ht y s hs (hline y hy)⟩
  have hB (y : G) (hy : y ∈ B) : Intertwines (κ.tprod ξ) (κ.tprod ξ) y ↔
      Intertwines (ξ.comp (Subgroup.inclusion hU)) (ξ.comp (Subgroup.inclusion hU)) y := by
    obtain ⟨e⟩ := E y hy
    rw [intertwines_restrict_iff_of_domain_product hK hU ξ ht y (hD y hy)]
    exact ⟨fun ⟨f, hf⟩ => ⟨e.symm f, fun h => hf (e.symm.map_eq_zero_iff.mp h)⟩,
      fun ⟨f, hf⟩ => ⟨e f, fun h => hf (e.map_eq_zero_iff.mp h)⟩⟩
  refine ⟨?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨ay, hay, b, hb, rfl⟩ := Set.mem_mul.mp (hsupport
        (intertwines_restriction_of_tprod hK κ ξ ht x hx))
      obtain ⟨a, ha, y, hy, rfl⟩ := Set.mem_mul.mp hay
      apply Set.mul_mem_mul _ (hK hb)
      refine Set.mul_mem_mul (hK ha) ⟨hy, (hB y hy).mp (?_ : Intertwines (κ.tprod ξ) (κ.tprod ξ) y)⟩
      exact (intertwines_mul_left_right_iff (κ.tprod ξ) y ⟨a, hK ha⟩ ⟨b, hK hb⟩).mp hx
    · intro hx
      obtain ⟨ay, hay, b, hb, rfl⟩ := Set.mem_mul.mp hx
      obtain ⟨a, ha, y, ⟨hy, hξy⟩, rfl⟩ := Set.mem_mul.mp hay
      exact (intertwines_mul_left_right_iff (κ.tprod ξ) y ⟨a, ha⟩ ⟨b, hb⟩).mpr ((hB y hy).mpr hξy)
  · intro y hy
    obtain ⟨e⟩ := E y hy
    exact e.symm.finrank_eq

end Twist

end Langlands.BushnellKutzko
