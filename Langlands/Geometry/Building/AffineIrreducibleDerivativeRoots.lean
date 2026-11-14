import Langlands.Geometry.Building.AffineIrreducibleSimpleRoots
import Langlands.Geometry.Building.AffineDerivativeRootPairing
import Mathlib.LinearAlgebra.RootSystem.Irreducible
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-!
# Irreducibility of an affine root system through its derivative roots

An affine root system `Ψ` is irreducible (KP Definition 1.3.13, `IsIrreducibleRoots`) exactly
when its finite root pairing of derivatives admits no partition of its roots into two nonempty
mutually orthogonal parts. For a root system over a field of characteristic different from `2`
this partition property, together with nonemptiness, is Mathlib's `RootPairing.IsIrreducible`.
Since it depends only on the zero pattern of the pairing, it transfers along any bijection of
roots preserving that pattern, also between different coefficient fields.
-/

noncomputable section

open Set Module

/-! ### Irreducibility of root systems through orthogonal partitions -/

namespace RootPairing

variable {ι K M N : Type*} [Field K] [NeZero (2 : K)]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- A root system over a field of characteristic different from `2` is irreducible exactly when
it has a root and no partition of its roots into two nonempty mutually orthogonal parts. -/
theorem isIrreducible_iff_forall_isOrthogonal (P : RootPairing ι K M N) [P.IsRootSystem] :
    P.IsIrreducible ↔ Nonempty ι ∧
      ∀ s : Set ι, (∀ i ∈ s, ∀ j ∉ s, P.IsOrthogonal i j) → s = ∅ ∨ s = univ := by
  constructor
  · intro hP
    have hne : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      have htop : Submodule.span K (range P.root) = ⊤ := IsRootSystem.span_root_eq_top
      rw [range_eq_empty, Submodule.span_empty] at htop
      have : Subsingleton M := (Submodule.subsingleton_iff K).mp (subsingleton_of_bot_eq_top htop)
      exact not_nontrivial M hP.nontrivial
    refine ⟨hne, fun s hs => ?_⟩
    rcases s.eq_empty_or_nonempty with h | hsne
    · exact Or.inl h
    right
    have hspan : Submodule.span K (P.root '' s) = ⊤ := by
      refine P.span_root_image_eq_top_of_forall_orthogonal s hsne fun j hj i hi => ?_
      by_cases hjs : j ∈ s
      · exact absurd (Submodule.subset_span (mem_image_of_mem _ hjs)) hj
      · exact (hs i hi j hjs).symm
    refine eq_univ_of_forall fun j => ?_
    by_contra hjs
    have hker : Submodule.span K (P.root '' s) ≤ LinearMap.ker (P.coroot' j) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, root_coroot'_eq_pairing]
      exact (hs i hi j hjs).1
    rw [hspan] at hker
    have h2 : P.coroot' j (P.root j) = 0 := LinearMap.mem_ker.mp (hker Submodule.mem_top)
    rw [root_coroot'_eq_pairing, pairing_same] at h2
    exact two_ne_zero h2
  · rintro ⟨⟨i₀⟩, hs⟩
    have : Nontrivial M := ⟨⟨P.root i₀, 0, P.ne_zero i₀⟩⟩
    refine IsIrreducible.mk' P fun q hq₁ hq₀ => ?_
    refine P.eq_top_of_mem_invtSubmodule_of_forall_eq_univ q hq₀ hq₁ fun Φ hΦ hroot hker => ?_
    refine (hs Φ fun i hi j hj => ?_).resolve_left hΦ.ne_empty
    have hij : P.pairing i j = 0 := by
      rw [← root_coroot'_eq_pairing]
      exact LinearMap.mem_ker.mp (hker j hj (hroot (mem_image_of_mem _ hi)))
    exact ⟨hij, P.pairing_eq_zero_iff'.mp hij⟩

/-- Irreducibility of root systems, possibly over different fields, transfers along a bijection
of their roots which preserves the vanishing of the root–coroot pairings. -/
theorem isIrreducible_iff_of_equiv_pairing_eq_zero {ι' K' M' N' : Type*} [Field K']
    [NeZero (2 : K')] [AddCommGroup M'] [Module K' M'] [AddCommGroup N'] [Module K' N']
    (P : RootPairing ι K M N) (P' : RootPairing ι' K' M' N') [P.IsRootSystem]
    [P'.IsRootSystem] (e : ι ≃ ι')
    (he : ∀ i j, P.pairing i j = 0 ↔ P'.pairing (e i) (e j) = 0) :
    P.IsIrreducible ↔ P'.IsIrreducible := by
  have horth : ∀ i j, P.IsOrthogonal i j ↔ P'.IsOrthogonal (e i) (e j) := fun i j => by
    simp only [IsOrthogonal, he]
  rw [isIrreducible_iff_forall_isOrthogonal, isIrreducible_iff_forall_isOrthogonal,
    e.nonempty_congr]
  refine and_congr_right fun _ => ⟨fun h s' hs' => ?_, fun h s hs => ?_⟩
  · have := h (e ⁻¹' s') fun i hi j hj => (horth i j).mpr (hs' _ hi _ hj)
    rcases this with h₀ | h₁
    · left
      rw [← e.image_preimage s', h₀, image_empty]
    · right
      rw [← e.image_preimage s', h₁, image_univ, e.range_eq_univ]
  · have := h (e.symm ⁻¹' s) fun i' hi' j' hj' => by
      have := (horth (e.symm i') (e.symm j')).mp (hs _ hi' _ hj')
      simpa only [Equiv.apply_symm_apply] using this
    rcases this with h₀ | h₁
    · left
      rw [← e.symm.image_preimage s, h₀, image_empty]
    · right
      rw [← e.symm.image_preimage s, h₁, image_univ, e.symm.range_eq_univ]

end RootPairing

/-! ### Affine root systems -/

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

namespace IsAffineRootSystemWithRankZero

variable (hΨ : IsAffineRootSystemWithRankZero Ψ)

include hΨ

/-- The pairing of two derivative roots is the value of the first derivative at any coroot
vector of any affine root with the second derivative. -/
theorem derivativePairing_pairing_eq {ψ η : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) (hη : η ∈ Ψ) {v : V}
    (hv : IsCoroot Ψ η v) :
    hΨ.derivativePairing.pairing ⟨ψ.linear, linear_mem_derivativeRoots hψ⟩
      ⟨η.linear, linear_mem_derivativeRoots hη⟩ = ψ.linear v := by
  change ψ.linear (hΨ.derivativeCoroot ⟨η.linear, linear_mem_derivativeRoots hη⟩) = ψ.linear v
  congr 1
  exact hΨ.coroot_eq_of_linear_eq (hΨ.isCoroot_derivativeCoroot _) hv
    (hΨ.linear_derivativeRootLift ⟨η.linear, linear_mem_derivativeRoots hη⟩).symm

/-- `Ψ` is irreducible (KP Definition 1.3.13) exactly when no partition of its derivative roots
into two parts is orthogonal for the derivative root pairing, unless one part is empty. -/
theorem isIrreducibleRoots_iff_forall_isOrthogonal :
    IsIrreducibleRoots Ψ ↔ ∀ s : Set (derivativeRoots Ψ),
      (∀ a ∈ s, ∀ b ∉ s, hΨ.derivativePairing.IsOrthogonal a b) → s = ∅ ∨ s = univ := by
  constructor
  · intro hirr s hs
    let Ψ₁ : Set (A →ᵃ[ℝ] ℝ) :=
      {ψ | ∃ h : ψ ∈ Ψ, (⟨ψ.linear, linear_mem_derivativeRoots h⟩ : derivativeRoots Ψ) ∈ s}
    let Ψ₂ : Set (A →ᵃ[ℝ] ℝ) :=
      {ψ | ∃ h : ψ ∈ Ψ, (⟨ψ.linear, linear_mem_derivativeRoots h⟩ : derivativeRoots Ψ) ∉ s}
    have hunion : Ψ₁ ∪ Ψ₂ = Ψ := by
      ext ψ
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
      · intro h
        by_cases hs' : (⟨ψ.linear, linear_mem_derivativeRoots h⟩ : derivativeRoots Ψ) ∈ s
        · exact Or.inl ⟨h, hs'⟩
        · exact Or.inr ⟨h, hs'⟩
    have horth : RootsOrthogonal Ψ Ψ₁ Ψ₂ := by
      rintro ψ ⟨hψ, hψs⟩ η ⟨hη, hηs⟩ u v hu hv
      have hab := hs _ hψs _ hηs
      refine ⟨?_, ?_⟩
      · rw [← hΨ.derivativePairing_pairing_eq hψ hη hv]
        exact hab.1
      · rw [← hΨ.derivativePairing_pairing_eq hη hψ hu]
        exact hab.2
    rcases hirr Ψ₁ Ψ₂ hunion horth with h₁ | h₂
    · left
      refine eq_empty_of_forall_notMem fun a ha => ?_
      have hmem : hΨ.derivativeRootLift a ∈ Ψ₁ := by
        refine ⟨hΨ.derivativeRootLift_mem a, ?_⟩
        convert ha using 1
        exact Subtype.ext (hΨ.linear_derivativeRootLift a)
      rw [h₁] at hmem
      exact hmem
    · right
      refine eq_univ_of_forall fun a => ?_
      by_contra ha
      have hmem : hΨ.derivativeRootLift a ∈ Ψ₂ := by
        refine ⟨hΨ.derivativeRootLift_mem a, ?_⟩
        convert ha using 2
        exact Subtype.ext (hΨ.linear_derivativeRootLift a)
      rw [h₂] at hmem
      exact hmem
  · intro h Ψ₁ Ψ₂ hunion horth
    have hmem₁ : ∀ ψ ∈ Ψ₁, ψ ∈ Ψ := fun ψ hψ => hunion ▸ Or.inl hψ
    have hmem₂ : ∀ ψ ∈ Ψ₂, ψ ∈ Ψ := fun ψ hψ => hunion ▸ Or.inr hψ
    let s : Set (derivativeRoots Ψ) := {a | ∃ ψ ∈ Ψ₁, ψ.linear = a.val}
    have hs : ∀ a ∈ s, ∀ b ∉ s, hΨ.derivativePairing.IsOrthogonal a b := by
      rintro a ⟨ψ, hψ, hψa⟩ b hb
      have hη : hΨ.derivativeRootLift b ∈ Ψ₂ := by
        have hmem : hΨ.derivativeRootLift b ∈ Ψ₁ ∪ Ψ₂ :=
          (Set.ext_iff.mp hunion _).mpr (hΨ.derivativeRootLift_mem b)
        refine hmem.resolve_left fun h₁ => hb ⟨_, h₁, hΨ.linear_derivativeRootLift b⟩
      have hb' : b = ⟨(hΨ.derivativeRootLift b).linear,
          linear_mem_derivativeRoots (hΨ.derivativeRootLift_mem b)⟩ :=
        Subtype.ext (hΨ.linear_derivativeRootLift b).symm
      have hψ' : a = ⟨ψ.linear, linear_mem_derivativeRoots (hmem₁ ψ hψ)⟩ :=
        Subtype.ext hψa.symm
      obtain ⟨u, hu⟩ := hΨ.exists_isCoroot ψ (hmem₁ ψ hψ)
      obtain ⟨v, hv⟩ := hΨ.exists_isCoroot _ (hΨ.derivativeRootLift_mem b)
      have ho := horth ψ hψ _ hη u v hu hv
      rw [hb', hψ']
      exact ⟨by rw [hΨ.derivativePairing_pairing_eq (hmem₁ ψ hψ) (hmem₂ _ hη) hv]; exact ho.1,
        by rw [hΨ.derivativePairing_pairing_eq (hmem₂ _ hη) (hmem₁ ψ hψ) hu]; exact ho.2⟩
    rcases h s hs with h₀ | h₁
    · left
      refine eq_empty_of_forall_notMem fun ψ hψ => ?_
      have : (⟨ψ.linear, linear_mem_derivativeRoots (hmem₁ ψ hψ)⟩ : derivativeRoots Ψ) ∈ s :=
        ⟨ψ, hψ, rfl⟩
      rw [h₀] at this
      exact this
    · right
      refine eq_empty_of_forall_notMem fun η hη => ?_
      have : (⟨η.linear, linear_mem_derivativeRoots (hmem₂ η hη)⟩ : derivativeRoots Ψ) ∈ s := by
        rw [h₁]
        exact mem_univ _
      obtain ⟨ψ, hψ, hlin⟩ := this
      obtain ⟨u, hu⟩ := hΨ.exists_isCoroot ψ (hmem₁ ψ hψ)
      obtain ⟨v, hv⟩ := hΨ.exists_isCoroot η (hmem₂ η hη)
      have h0 := (horth ψ hψ η hη u v hu hv).1
      rw [hlin, hv.1] at h0
      exact two_ne_zero h0

/-- `Ψ` is irreducible (KP Definition 1.3.13) exactly when it is empty or its finite root
pairing of derivatives is irreducible in Mathlib's sense. -/
theorem isIrreducibleRoots_iff_isIrreducible :
    IsIrreducibleRoots Ψ ↔ Ψ = ∅ ∨ hΨ.derivativePairing.IsIrreducible := by
  rw [RootPairing.isIrreducible_iff_forall_isOrthogonal,
    hΨ.isIrreducibleRoots_iff_forall_isOrthogonal]
  constructor
  · intro h
    rcases Ψ.eq_empty_or_nonempty with hΨ₀ | ⟨ψ, hψ⟩
    · exact Or.inl hΨ₀
    · exact Or.inr ⟨⟨⟨ψ.linear, linear_mem_derivativeRoots hψ⟩⟩, h⟩
  · rintro (hΨ₀ | ⟨-, h⟩)
    · intro s _
      left
      refine eq_empty_of_forall_notMem fun a _ => ?_
      obtain ⟨ψ, hψ, -⟩ := a.property
      rw [hΨ₀] at hψ
      exact hψ
    · exact h

/-- A nonempty affine root system is irreducible (KP Definition 1.3.13) exactly when its finite
root pairing of derivatives is irreducible. -/
theorem isIrreducible_iff_isIrreducibleRoots (hne : Ψ.Nonempty) :
    hΨ.derivativePairing.IsIrreducible ↔ IsIrreducibleRoots Ψ := by
  rw [hΨ.isIrreducibleRoots_iff_isIrreducible, or_iff_right hne.ne_empty]

/-- Transfer of irreducibility from a root system `P` over any field of characteristic different
from `2`: if a bijection from its roots to the derivative roots of `Ψ` matches the vanishing of
the pairing of `P` with the vanishing of `a ↦ a(b∨)` on derivative roots, then `P` is irreducible
exactly when `Ψ` is nonempty and irreducible. -/
theorem isIrreducible_iff_isIrreducibleRoots_of_equiv {ι K M N : Type*} [Field K]
    [NeZero (2 : K)] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (P : RootPairing ι K M N) [P.IsRootSystem] (e : ι ≃ derivativeRoots Ψ)
    (he : ∀ i j, P.pairing i j = 0 ↔ (e i).val (hΨ.derivativeCoroot (e j)) = 0) :
    P.IsIrreducible ↔ Ψ.Nonempty ∧ IsIrreducibleRoots Ψ := by
  rw [RootPairing.isIrreducible_iff_of_equiv_pairing_eq_zero P hΨ.derivativePairing e he,
    hΨ.isIrreducibleRoots_iff_isIrreducible]
  constructor
  · intro h
    refine ⟨?_, Or.inr h⟩
    obtain ⟨a⟩ := ((RootPairing.isIrreducible_iff_forall_isOrthogonal _).mp h).1
    obtain ⟨ψ, hψ, -⟩ := a.property
    exact ⟨ψ, hψ⟩
  · rintro ⟨hne, h | h⟩
    · exact absurd h hne.ne_empty
    · exact h

end IsAffineRootSystemWithRankZero

end Langlands.Geometry.Building.AffineRootSystem
