import Langlands.Representation.Finite.Induction
import Langlands.Representation.Geometric.ClosedSubgroupDefinitions
import Langlands.Representation.Twist.Definitions
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Tactic.Group

/-! # Endomorphisms of the coinduction of a character -/

noncomputable section

open Module Representation

namespace Langlands.FiniteRep

open Geometric

variable {G : Type*} [Group G] (H : Subgroup G) (χ : H →* ℂˣ)

/-- The one-dimensional complex representation belonging to a unit-valued character. -/
def characterFDRep : FDRep ℂ H := FDRep.of (characterRepresentation χ)

private theorem characterRepresentation_apply (h : H) (z : ℂ) :
    characterRepresentation χ h z = (χ h : ℂ) * z := rfl

/-- The two restrictions of the character agree on the double-coset stabilizer. -/
def IsCharacterCompatible (w : G) : Prop :=
  ∀ x : orbitStabilizer H H w, χ x.val = χ (stabilizerToInducing H H w x)

open Classical in
/-- The stabilizer intertwining space has dimension one exactly when the characters agree. -/
theorem finrank_intertwiningMap_character (w : G) :
    finrank ℂ (IntertwiningMap ((characterRepresentation χ).comp (orbitStabilizer H H w).subtype)
      ((characterRepresentation χ).comp (stabilizerToInducing H H w))) =
      if IsCharacterCompatible H χ w then 1 else 0 := by
  let ρ : Representation ℂ (orbitStabilizer H H w) ℂ :=
    (characterRepresentation χ).comp (orbitStabilizer H H w).subtype
  let σ : Representation ℂ (orbitStabilizer H H w) ℂ :=
    (characterRepresentation χ).comp (stabilizerToInducing H H w)
  change finrank ℂ (IntertwiningMap ρ σ) = _
  by_cases h : IsCharacterCompatible H χ w
  · rw [ite_eq_left h]
    have heq : σ = ρ := by
      apply MonoidHom.ext
      intro x
      apply LinearMap.ext
      intro z
      change (χ (stabilizerToInducing H H w x) : ℂ) * z = (χ x.val : ℂ) * z
      rw [h x]
    rw [heq]
    have hinj := IntertwiningMap.toLinearMap_injective ρ ρ
    have hd := LinearMap.finrank_le_finrank_of_injective
      (f := IntertwiningMap.toLinearMapl (ρ := ρ) (σ := ρ)) hinj
    have hpos : 0 < finrank ℂ (IntertwiningMap ρ ρ) := by
      apply Module.finrank_pos_iff.mpr
      refine ⟨⟨IntertwiningMap.id ρ, 0, ?_⟩⟩
      intro heq
      have hv := DFunLike.congr_fun heq (1 : ℂ)
      simp at hv
    rw [Module.finrank_linearMap, Module.finrank_self, mul_one] at hd
    omega
  · rw [ite_eq_right h]
    unfold IsCharacterCompatible at h
    push Not at h
    obtain ⟨x, hx⟩ := h
    have hzero (F : IntertwiningMap ρ σ) : F = 0 := by
      have hc := IntertwiningMap.isIntertwining ρ σ F x (1 : ℂ)
      change F ((χ x.val : ℂ) * 1) = (χ (stabilizerToInducing H H w x) : ℂ) * F 1 at hc
      rw [← smul_eq_mul, map_smul, smul_eq_mul] at hc
      have hF : F 1 = 0 := by
        by_contra hn
        exact hx (Units.ext (mul_right_cancel₀ hn hc))
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro v
      have hs := map_smul F v (1 : ℂ)
      rw [smul_eq_mul, mul_one, hF, smul_zero] at hs
      exact hs
    let : Subsingleton (IntertwiningMap ρ σ) := ⟨fun F F' => (hzero F).trans (hzero F').symm⟩
    exact Module.finrank_zero_of_subsingleton

private abbrev CoindV := Representation.coindV H.subtype (characterRepresentation χ)

/-- Coinduction of a one-dimensional character in the model by covariant functions. -/
abbrev characterCoind (χ : H →* ℂˣ) :=
  Representation.coind H.subtype (characterRepresentation χ)

/-- The endomorphism algebra of the character's coinduction. -/
abbrev CharacterCoindEnd := IntertwiningMap (characterCoind H χ) (characterCoind H χ)

private def charEval (g : G) : CoindV H χ →ₗ[ℂ] ℂ :=
  LinearMap.proj g ∘ₗ (CoindV H χ).subtype

@[simp] private theorem charEval_apply (g : G) (f : CoindV H χ) : charEval H χ g f = f.val g := rfl

private theorem charCoind_apply (g x : G) (f : CoindV H χ) :
    (characterCoind H χ g f).val x = f.val (x * g) := rfl

private theorem coind_covariant (f : CoindV H χ) (h : H) (g : G) :
    f.val (h.val * g) = (χ h : ℂ) * f.val g := f.property h g

open Classical in
/-- The function supported on the subgroup with value one at the identity. -/
private def coindDelta : CoindV H χ := by
  let e (g : G) := if h : g ∈ H then (χ ⟨g, h⟩ : ℂ) else 0
  refine ⟨e, fun h g => ?_⟩
  change e (h.val * g) = (χ h : ℂ) * e g
  by_cases hg : g ∈ H
  · simp only [e, dite_eq_left (H.mul_mem h.property hg), dite_eq_left hg]
    change (χ (h * ⟨g, hg⟩) : ℂ) = _
    rw [map_mul, Units.val_mul]
  · simp only [e, dite_eq_right hg, dite_eq_right (mt (H.mul_mem_cancel_left h.property).mp hg),
      mul_zero]

private theorem coindDelta_right (h : H) :
    characterCoind H χ h.val (coindDelta H χ) = (χ h : ℂ) • coindDelta H χ := by
  classical
  apply Subtype.ext
  funext g
  change (coindDelta H χ).val (g * h.val) = (χ h : ℂ) * (coindDelta H χ).val g
  by_cases hg : g ∈ H
  · simp only [coindDelta, dite_eq_left hg, dite_eq_left (H.mul_mem hg h.property)]
    change (χ (⟨g, hg⟩ * h) : ℂ) = _
    rw [map_mul, Units.val_mul, mul_comm]
  · simp only [coindDelta, dite_eq_right hg,
      dite_eq_right (mt (H.mul_mem_cancel_right h.property).mp hg), mul_zero]

private theorem coindDelta_expansion [Fintype G] (f : CoindV H χ) :
    f = (Nat.card H : ℂ)⁻¹ •
      ∑ x : G, f.val x • characterCoind H χ x⁻¹ (coindDelta H χ) := by
  classical
  let : Fintype H := inferInstanceAs (Fintype {g : G // g ∈ (H : Set G)})
  apply Subtype.ext
  funext g
  change f.val g = charEval H χ g ((Nat.card H : ℂ)⁻¹ • ∑ x : G,
    f.val x • characterCoind H χ x⁻¹ (coindDelta H χ))
  simp only [map_smul, map_sum, charEval_apply, charCoind_apply, smul_eq_mul]
  rw [← Equiv.sum_comp (Equiv.mulRight g) (fun x : G => f.val x * (coindDelta H χ).val (g * x⁻¹))]
  have he : (∑ x : G, f.val (x * g) * (coindDelta H χ).val (g * (x * g)⁻¹)) =
      ∑ _ : H, f.val g := by
    refine Finset.sum_congr_set (H : Set G) _ (fun _ : H => f.val g) (fun x hx => ?_) (fun x hx => ?_)
    · rw [show g * (x * g)⁻¹ = x⁻¹ by group]
      change f.val ((⟨x, hx⟩ : H).val * g) * (coindDelta H χ).val x⁻¹ = f.val g
      rw [coind_covariant H χ f ⟨x, hx⟩ g]
      simp only [coindDelta, dite_eq_left (H.inv_mem hx)]
      change ((χ ⟨x, hx⟩ : ℂ) * f.val g) * (χ ((⟨x, hx⟩ : H)⁻¹) : ℂ) = f.val g
      rw [mul_right_comm, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mul]
    · rw [show g * (x * g)⁻¹ = x⁻¹ by group]
      simp only [coindDelta, dite_eq_right (show x⁻¹ ∉ H from fun hi => hx (H.inv_mem_iff.mp hi)),
        mul_zero]
  change f.val g = (Nat.card H : ℂ)⁻¹ * ∑ x : G,
    f.val (x * g) * (coindDelta H χ).val (g * (x * g)⁻¹)
  rw [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, ← mul_assoc]
  rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]

/-- The kernel of an intertwiner is its value on the normalized subgroup-supported function. -/
def characterCoindKernel (T : CharacterCoindEnd H χ) : G → ℂ := (T (coindDelta H χ)).val

private theorem charEnd_intertwines (T : CharacterCoindEnd H χ) (g : G) (f : CoindV H χ) :
    T (characterCoind H χ g f) = characterCoind H χ g (T f) :=
  IntertwiningMap.isIntertwining (characterCoind H χ) (characterCoind H χ) T g f

private theorem charEnd_apply [Fintype G] (T : CharacterCoindEnd H χ) (f : CoindV H χ) (g : G) :
    (T f).val g = (Nat.card H : ℂ)⁻¹ * ∑ x : G, f.val x * characterCoindKernel H χ T (g * x⁻¹) := by
  calc
    _ = charEval H χ g (T ((Nat.card H : ℂ)⁻¹ • ∑ x : G,
        f.val x • characterCoind H χ x⁻¹ (coindDelta H χ))) :=
      congrArg (fun v : CoindV H χ => charEval H χ g (T v)) (coindDelta_expansion H χ f)
    _ = _ := by
      simp only [map_smul, map_sum, charEnd_intertwines, charEval_apply, charCoind_apply,
        smul_eq_mul, characterCoindKernel]

/-- The kernel determines the operator. -/
theorem characterCoindKernel_injective [Fintype G] : Function.Injective (characterCoindKernel H χ) := by
  intro S T h
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext g
  change (S f).val g = (T f).val g
  rw [charEnd_apply, charEnd_apply, h]

private theorem charKernel_mul [Fintype G] (S T : CharacterCoindEnd H χ) (g : G) :
    characterCoindKernel H χ (S * T) g = (Nat.card H : ℂ)⁻¹ *
      ∑ x : G, characterCoindKernel H χ T x * characterCoindKernel H χ S (g * x⁻¹) :=
  charEnd_apply H χ S (T (coindDelta H χ)) g

private def IsBiCovariant (f : G → ℂ) : Prop :=
  (∀ h : H, ∀ g : G, f (h.val * g) = (χ h : ℂ) * f g) ∧
    (∀ h : H, ∀ g : G, f (g * h.val) = (χ h : ℂ) * f g)

private theorem charKernel_covariant (T : CharacterCoindEnd H χ) :
    IsBiCovariant H χ (characterCoindKernel H χ T) := by
  refine ⟨coind_covariant H χ (T (coindDelta H χ)), ?_⟩
  intro h g
  change (characterCoind H χ h.val (T (coindDelta H χ))).val g =
    (χ h : ℂ) * (T (coindDelta H χ)).val g
  rw [← charEnd_intertwines, coindDelta_right, map_smul]
  rfl

private theorem compatible_of_covariant_ne_zero {f : G → ℂ} (hf : IsBiCovariant H χ f)
    {g : G} (h : f g ≠ 0) : IsCharacterCompatible H χ g := by
  intro x
  have he : x.val.val * g = g * (stabilizerToInducing H H g x).val := by
    rw [stabilizerToInducing_apply]
    group
  have hc := (hf.1 x.val g).symm.trans ((congrArg f he).trans (hf.2 (stabilizerToInducing H H g x) g))
  exact Units.ext (mul_right_cancel₀ h hc)

section Anti

variable (a : G ≃ G) (ha : ∀ x y : G, a (x * y) = a y * a x)
  (aH : H → H) (haH : ∀ h : H, (aH h).val = a h.val) (hχ : ∀ h : H, χ (aH h) = χ h)

include ha aH haH hχ

private theorem kernel_anti_invariant {ι : Type*} (r : ι → G)
    (hsurj : Function.Surjective (fun i => DoubleCoset.mk H H (r i)))
    (hfix : ∀ i, IsCharacterCompatible H χ (r i) → a (r i) = r i)
    (T : CharacterCoindEnd H χ) (g : G) :
    characterCoindKernel H χ T (a g) = characterCoindKernel H χ T g := by
  let f := characterCoindKernel H χ T
  have hf : IsBiCovariant H χ f := charKernel_covariant H χ T
  have hf' : IsBiCovariant H χ (f ∘ a) := by
    constructor <;> intro h x <;> simp only [Function.comp_apply, ha]
    · rw [← haH h, hf.2 (aH h) (a x), hχ h]
    · rw [← haH h, hf.1 (aH h) (a x), hχ h]
  obtain ⟨i, hi⟩ := hsurj (DoubleCoset.mk H H g)
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.eq.mp hi
  have he (i : ι) : (f ∘ a) (r i) = f (r i) := by
    by_cases hc : IsCharacterCompatible H χ (r i)
    · simp [hfix i hc]
    · have h₁ : f (r i) = 0 := not_not.mp (mt (compatible_of_covariant_ne_zero H χ hf) hc)
      have h₂ : (f ∘ a) (r i) = 0 := not_not.mp (mt (compatible_of_covariant_ne_zero H χ hf') hc)
      rw [h₂, h₁]
  change (f ∘ a) ((⟨x, hx⟩ : H).val * r i * (⟨y, hy⟩ : H).val) =
      f ((⟨x, hx⟩ : H).val * r i * (⟨y, hy⟩ : H).val)
  rw [hf'.2, hf'.1, hf.2, hf.1, he]

/-- A character-preserving group antiautomorphism that fixes the compatible representatives
acts trivially on these kernels and reverses their convolution product. -/
theorem characterCoindEnd_mul_comm_of_anti [Fintype G] {ι : Type*} (r : ι → G)
    (hsurj : Function.Surjective (fun i => DoubleCoset.mk H H (r i)))
    (hfix : ∀ i, IsCharacterCompatible H χ (r i) → a (r i) = r i)
    (S T : CharacterCoindEnd H χ) : S * T = T * S := by
  have hinv := kernel_anti_invariant H χ a ha aH haH hχ r hsurj hfix
  have ha1 : a 1 = 1 := by
    have he := ha (1 : G) 1
    rw [mul_one] at he
    exact mul_left_cancel (show a 1 * a 1 = a 1 * 1 by rw [mul_one, ← he])
  have haInv (x : G) : a x⁻¹ = (a x)⁻¹ := by
    have he := ha x x⁻¹
    rw [mul_inv_cancel, ha1] at he
    exact eq_inv_of_mul_eq_one_left he.symm
  apply characterCoindKernel_injective H χ
  funext g
  rw [← hinv (S * T) g, charKernel_mul, charKernel_mul]
  congr 1
  let e : G ≃ G := (Equiv.inv G).trans ((Equiv.mulLeft g).trans a)
  refine Fintype.sum_equiv e _ _ (fun y => ?_) |>.symm
  change characterCoindKernel H χ S y * characterCoindKernel H χ T (g * y⁻¹) =
    characterCoindKernel H χ T (a (g * y⁻¹)) *
      characterCoindKernel H χ S (a g * (a (g * y⁻¹))⁻¹)
  have he : a g * (a (g * y⁻¹))⁻¹ = a y := by rw [ha, haInv y]; group
  rw [he, hinv T, hinv S, mul_comm]

end Anti

end Langlands.FiniteRep
