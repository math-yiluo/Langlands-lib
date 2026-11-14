import Langlands.Automorphic.PlaceComponentMinimal
import Langlands.Representation.CompactMaschke

/-!
# Detecting stable subspaces by a compact type

Let `κ` be a representation of a compact group `K` and `π` a Lie action on a complex vector
space `V`, where `κ` is locally finite (every vector lies in a finite-dimensional `K`-stable
subspace) and weakly continuous (every linear form of every orbit map is continuous). Fix a
continuous matrix representation `τ` of `K`. A stable subspace is `τ`-free if it has no
nonzero `τ`-intertwiner.

This module shows that the vectors whose stable hull is `τ`-free form a subspace
`freeSet κ π d τ`, preserved by `κ`, `π` and every linear operator commuting with them. When
that subspace is zero, every nonzero stable subspace has a nonzero `τ`-intertwiner
(`intertwiners_ne_bot_of_freeSet_eq_bot`). The key input is the lifting of intertwiners
through equivariant surjections (`CompactMaschke.exists_lift_intertwiner`).
-/

noncomputable section

open scoped Matrix

set_option autoImplicit false

namespace Langlands.Automorphic.PlaceComponent

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Group K] [TopologicalSpace K] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  {V : Type*} [AddCommGroup V] [Module ℂ V]

/-! ### Local finiteness and weak continuity -/

/-- Every vector lies in a finite-dimensional `K`-stable subspace. -/
def IsLocallyFinite (κ : Representation ℂ K V) : Prop :=
  ∀ x : V, ∃ E : Submodule ℂ V, FiniteDimensional ℂ E ∧ x ∈ E ∧
    ∀ (k : K), ∀ y ∈ E, κ k y ∈ E

/-- Every linear form of every orbit map is continuous. -/
def IsWeaklyContinuous (κ : Representation ℂ K V) : Prop :=
  ∀ (μ : V →ₗ[ℂ] ℂ) (x : V), Continuous fun k => μ (κ k x)

/-- The restriction of `κ` to a `K`-stable subspace. -/
def restrictRep (κ : Representation ℂ K V) (W : Submodule ℂ V)
    (hW : ∀ (k : K), ∀ x ∈ W, κ k x ∈ W) : Representation ℂ K W :=
  Subrepresentation.toRepresentation ⟨W, fun k x hx => hW k x hx⟩

omit [TopologicalSpace K] in
theorem restrictRep_apply (κ : Representation ℂ K V) (W : Submodule ℂ V)
    (hW : ∀ (k : K), ∀ x ∈ W, κ k x ∈ W) (k : K) (x : W) :
    ((restrictRep κ W hW k x : W) : V) = κ k x := rfl

omit [TopologicalSpace K] in
theorem isLocallyFinite_restrict {κ : Representation ℂ K V} (hκ : IsLocallyFinite κ)
    {W : Submodule ℂ V} (hW : ∀ (k : K), ∀ x ∈ W, κ k x ∈ W) :
    IsLocallyFinite (restrictRep κ W hW) := by
  intro x
  obtain ⟨E, hE, hxE, hEs⟩ := hκ x
  refine ⟨E.comap W.subtype, ?_, hxE, fun k y hy => hEs k _ hy⟩
  let f : E.comap W.subtype →ₗ[ℂ] E := W.subtype.restrict fun y hy => hy
  have hf : Function.Injective f := fun a b h => by
    have h' := congrArg (fun z : E => (z : V)) h
    exact Subtype.ext (Subtype.ext h')
  exact Module.Finite.of_injective f hf

theorem isWeaklyContinuous_restrict {κ : Representation ℂ K V} (hκ : IsWeaklyContinuous κ)
    {W : Submodule ℂ V} (hW : ∀ (k : K), ∀ x ∈ W, κ k x ∈ W) :
    IsWeaklyContinuous (restrictRep κ W hW) := by
  intro μ x
  obtain ⟨g, hg⟩ := LinearMap.exists_extend μ
  have h : ∀ k, μ (restrictRep κ W hW k x) = g (κ k x) := fun k => by
    rw [← hg]
    rfl
  simp_rw [h]
  exact hκ g x

/-! ### Intertwiners into restricted representations -/

omit [TopologicalSpace K] in
theorem intertwiners_bot (κ : Representation ℂ K V) (d : ℕ)
    (τ : K →* Matrix (Fin d) (Fin d) ℂ) : intertwiners κ ⊥ d τ = ⊥ := by
  rw [eq_bot_iff]
  intro T hT
  rw [Submodule.mem_bot]
  exact LinearMap.ext fun x => (Submodule.mem_bot ℂ).mp (hT.1 x)

omit [TopologicalSpace K] in
theorem free_mono (κ : Representation ℂ K V) {W W' : Submodule ℂ V} (h : W' ≤ W) {d : ℕ}
    (τ : K →* Matrix (Fin d) (Fin d) ℂ) (hW : intertwiners κ W d τ = ⊥) :
    intertwiners κ W' d τ = ⊥ :=
  le_bot_iff.mp (hW ▸ intertwiners_mono κ h d τ)

omit [TopologicalSpace K] in
/-- An intertwiner into the restriction to a `τ`-free subspace vanishes. -/
theorem eq_zero_of_free (κ : Representation ℂ K V) {W : Submodule ℂ V}
    (hW : ∀ (k : K), ∀ x ∈ W, κ k x ∈ W) {d : ℕ} (τ : K →* Matrix (Fin d) (Fin d) ℂ)
    (hfree : intertwiners κ W d τ = ⊥) (ψ : (Fin d → ℂ) →ₗ[ℂ] W)
    (hψ : ∀ k x, ψ (τ k *ᵥ x) = restrictRep κ W hW k (ψ x)) : ψ = 0 := by
  have hmem : W.subtype ∘ₗ ψ ∈ intertwiners κ W d τ :=
    ⟨fun x => (ψ x).2, fun k x => by
      change ((ψ (τ k *ᵥ x) : W) : V) = κ k (ψ x)
      rw [hψ]
      rfl⟩
  rw [hfree, Submodule.mem_bot] at hmem
  exact LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun hmem x)

variable [IsTopologicalGroup K] [CompactSpace K]

/-- `τ`-freeness passes to images under operators commuting with `K`. -/
theorem free_map {κ : Representation ℂ K V} (hfin : IsLocallyFinite κ)
    (hweak : IsWeaklyContinuous κ) (A : V →ₗ[ℂ] V) (hA : ∀ k x, A (κ k x) = κ k (A x))
    {W : Submodule ℂ V} (hWs : ∀ (k : K), ∀ x ∈ W, κ k x ∈ W) {d : ℕ}
    (τ : K →* Matrix (Fin d) (Fin d) ℂ) (hW : intertwiners κ W d τ = ⊥) :
    intertwiners κ (W.map A) d τ = ⊥ := by
  rw [eq_bot_iff]
  intro ψ hψ
  rw [mem_intertwiners] at hψ
  rw [Submodule.mem_bot]
  obtain ⟨ψ', hψ'eq, hψ'q⟩ := CompactMaschke.exists_lift_intertwiner (restrictRep κ W hWs) κ
    (isLocallyFinite_restrict hfin hWs) (isWeaklyContinuous_restrict hweak hWs)
    (A ∘ₗ W.subtype) (fun k x => hA k x) τ ψ hψ.2 (fun x => by
      obtain ⟨y, hy, hxy⟩ := hψ.1 x
      exact ⟨⟨y, hy⟩, hxy⟩)
  rw [← hψ'q, eq_zero_of_free κ hWs τ hW ψ' hψ'eq, LinearMap.comp_zero]

/-- `τ`-freeness is preserved by sums of `K`-stable subspaces. -/
theorem free_sup {κ : Representation ℂ K V} (hfin : IsLocallyFinite κ)
    (hweak : IsWeaklyContinuous κ) {W₁ W₂ : Submodule ℂ V}
    (h₁s : ∀ (k : K), ∀ x ∈ W₁, κ k x ∈ W₁) (h₂s : ∀ (k : K), ∀ x ∈ W₂, κ k x ∈ W₂) {d : ℕ}
    (τ : K →* Matrix (Fin d) (Fin d) ℂ) (h₁ : intertwiners κ W₁ d τ = ⊥)
    (h₂ : intertwiners κ W₂ d τ = ⊥) : intertwiners κ (W₁ ⊔ W₂) d τ = ⊥ := by
  let ρ₁ := restrictRep κ W₁ h₁s
  let ρ₂ := restrictRep κ W₂ h₂s
  let ρ : Representation ℂ K (W₁ × W₂) := ρ₁.prod ρ₂
  let q : (W₁ × W₂) →ₗ[ℂ] V := W₁.subtype.coprod W₂.subtype
  have hq : ∀ k x, q (ρ k x) = κ k (q x) := fun k x => by
    change ((ρ₁ k x.1 : W₁) : V) + ((ρ₂ k x.2 : W₂) : V) = κ k ((x.1 : V) + (x.2 : V))
    rw [map_add]
    rfl
  have hρfin : ∀ x : W₁ × W₂, ∃ E : Submodule ℂ (W₁ × W₂), FiniteDimensional ℂ E ∧ x ∈ E ∧
      ∀ (k : K), ∀ y ∈ E, ρ k y ∈ E := by
    intro x
    obtain ⟨E₁, hE₁, hx₁, hE₁s⟩ := isLocallyFinite_restrict hfin h₁s x.1
    obtain ⟨E₂, hE₂, hx₂, hE₂s⟩ := isLocallyFinite_restrict hfin h₂s x.2
    refine ⟨E₁.map (LinearMap.inl ℂ W₁ W₂) ⊔ E₂.map (LinearMap.inr ℂ W₁ W₂), inferInstance,
      ?_, fun k y hy => ?_⟩
    · rw [show x = LinearMap.inl ℂ W₁ W₂ x.1 + LinearMap.inr ℂ W₁ W₂ x.2 by simp]
      exact Submodule.add_mem_sup ⟨x.1, hx₁, rfl⟩ ⟨x.2, hx₂, rfl⟩
    · obtain ⟨a, ⟨a', ha', rfl⟩, b, ⟨b', hb', rfl⟩, rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add]
      refine Submodule.add_mem_sup ⟨ρ₁ k a', hE₁s k a' ha', ?_⟩ ⟨ρ₂ k b', hE₂s k b' hb', ?_⟩
      · ext <;> simp [ρ]
      · ext <;> simp [ρ]
  have hρweak : ∀ (μ : (W₁ × W₂) →ₗ[ℂ] ℂ) (x : W₁ × W₂), Continuous fun k => μ (ρ k x) := by
    intro μ x
    have h : ∀ k, μ (ρ k x) = (μ ∘ₗ LinearMap.inl ℂ W₁ W₂) (ρ₁ k x.1) +
        (μ ∘ₗ LinearMap.inr ℂ W₁ W₂) (ρ₂ k x.2) := fun k => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← map_add]
      congr 1
      ext <;> simp [ρ]
    simp_rw [h]
    exact (isWeaklyContinuous_restrict hweak h₁s _ x.1).add
      (isWeaklyContinuous_restrict hweak h₂s _ x.2)
  rw [eq_bot_iff]
  intro ψ hψ
  rw [mem_intertwiners] at hψ
  rw [Submodule.mem_bot]
  obtain ⟨ψ', hψ'eq, hψ'q⟩ := CompactMaschke.exists_lift_intertwiner ρ κ hρfin hρweak q hq τ ψ
    hψ.2 (fun x => by
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hψ.1 x)
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩)
  have hfst : LinearMap.fst ℂ W₁ W₂ ∘ₗ ψ' = 0 := eq_zero_of_free κ h₁s τ h₁ _ fun k x => by
    simp only [LinearMap.comp_apply, hψ'eq]
    rfl
  have hsnd : LinearMap.snd ℂ W₁ W₂ ∘ₗ ψ' = 0 := eq_zero_of_free κ h₂s τ h₂ _ fun k x => by
    simp only [LinearMap.comp_apply, hψ'eq]
    rfl
  have hψ'0 : ψ' = 0 := LinearMap.ext fun x =>
    Prod.ext (LinearMap.congr_fun hfst x) (LinearMap.congr_fun hsnd x)
  rw [← hψ'q, hψ'0, LinearMap.comp_zero]

/-! ### Stable hulls and the free set -/

variable (κ : Representation ℂ K V) (π : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ V)

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] in
/-- The smallest stable subspace containing `x`. -/
def hull (x : V) : Submodule ℂ V := sInf {U | IsStable κ π U ∧ x ∈ U}

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] in
theorem hull_isStable (x : V) : IsStable κ π (hull κ π x) :=
  isStable_sInf κ π _ fun _ hU => hU.1

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] in
theorem mem_hull (x : V) : x ∈ hull κ π x :=
  Submodule.mem_sInf.mpr fun _ hU => hU.2

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] in
theorem hull_le {U : Submodule ℂ V} (hU : IsStable κ π U) {x : V} (hx : x ∈ U) :
    hull κ π x ≤ U :=
  sInf_le ⟨hU, hx⟩

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] in
theorem isStable_sup {W₁ W₂ : Submodule ℂ V} (h₁ : IsStable κ π W₁) (h₂ : IsStable κ π W₂) :
    IsStable κ π (W₁ ⊔ W₂) := by
  refine ⟨fun k x hx => ?_, fun X x hx => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (h₁.1 k a ha) (h₂.1 k b hb)
  · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (h₁.2 X a ha) (h₂.2 X b hb)

variable {κ} in
/-- The vectors whose stable hull has no nonzero `τ`-intertwiner. -/
def freeSet (hfin : IsLocallyFinite κ) (hweak : IsWeaklyContinuous κ) {d : ℕ}
    (τ : K →* Matrix (Fin d) (Fin d) ℂ) : Submodule ℂ V where
  carrier := {x | intertwiners κ (hull κ π x) d τ = ⊥}
  zero_mem' := by
    change intertwiners κ (hull κ π 0) d τ = ⊥
    refine free_mono κ (hull_le κ π ⟨fun _ _ hx => ?_, fun _ _ hx => ?_⟩ (Submodule.zero_mem ⊥))
      τ (intertwiners_bot κ d τ)
    · rw [(Submodule.mem_bot ℂ).mp hx, map_zero]
      exact Submodule.zero_mem _
    · rw [(Submodule.mem_bot ℂ).mp hx, map_zero]
      exact Submodule.zero_mem _
  add_mem' := by
    intro x y hx hy
    change intertwiners κ (hull κ π (x + y)) d τ = ⊥
    have hs := isStable_sup κ π (hull_isStable κ π x) (hull_isStable κ π y)
    refine free_mono κ (hull_le κ π hs (Submodule.add_mem_sup (mem_hull κ π x)
      (mem_hull κ π y))) τ ?_
    exact free_sup hfin hweak (hull_isStable κ π x).1 (hull_isStable κ π y).1 τ hx hy
  smul_mem' := by
    intro c x hx
    change intertwiners κ (hull κ π (c • x)) d τ = ⊥
    exact free_mono κ (hull_le κ π (hull_isStable κ π x)
      (Submodule.smul_mem _ c (mem_hull κ π x))) τ hx

variable {κ π}

theorem mem_freeSet {hfin : IsLocallyFinite κ} {hweak : IsWeaklyContinuous κ} {d : ℕ}
    {τ : K →* Matrix (Fin d) (Fin d) ℂ} {x : V} :
    x ∈ freeSet π hfin hweak τ ↔ intertwiners κ (hull κ π x) d τ = ⊥ := Iff.rfl

theorem freeSet_compact {hfin : IsLocallyFinite κ} {hweak : IsWeaklyContinuous κ} {d : ℕ}
    {τ : K →* Matrix (Fin d) (Fin d) ℂ} (k : K) {x : V} (hx : x ∈ freeSet π hfin hweak τ) :
    κ k x ∈ freeSet π hfin hweak τ :=
  free_mono κ (hull_le κ π (hull_isStable κ π x) ((hull_isStable κ π x).1 k x
    (mem_hull κ π x))) τ hx

theorem freeSet_lie {hfin : IsLocallyFinite κ} {hweak : IsWeaklyContinuous κ} {d : ℕ}
    {τ : K →* Matrix (Fin d) (Fin d) ℂ} (X : 𝔤) {x : V} (hx : x ∈ freeSet π hfin hweak τ) :
    π X x ∈ freeSet π hfin hweak τ :=
  free_mono κ (hull_le κ π (hull_isStable κ π x) ((hull_isStable κ π x).2 X x
    (mem_hull κ π x))) τ hx

/-- Operators commuting with both actions preserve the free set. -/
theorem freeSet_map {hfin : IsLocallyFinite κ} {hweak : IsWeaklyContinuous κ} {d : ℕ}
    {τ : K →* Matrix (Fin d) (Fin d) ℂ} (A : V →ₗ[ℂ] V) (hAκ : ∀ k x, A (κ k x) = κ k (A x))
    (hAπ : ∀ X x, A (π X x) = π X (A x)) {x : V} (hx : x ∈ freeSet π hfin hweak τ) :
    A x ∈ freeSet π hfin hweak τ := by
  have hs : IsStable κ π ((hull κ π x).map A) := by
    refine ⟨?_, ?_⟩
    · rintro k _ ⟨y, hy, rfl⟩
      exact ⟨κ k y, (hull_isStable κ π x).1 k y hy, hAκ k y⟩
    · rintro X _ ⟨y, hy, rfl⟩
      exact ⟨π X y, (hull_isStable κ π x).2 X y hy, hAπ X y⟩
  exact free_mono κ (hull_le κ π hs ⟨x, mem_hull κ π x, rfl⟩) τ
    (free_map hfin hweak A hAκ (hull_isStable κ π x).1 τ hx)

/-- A nonzero vector is not free for the matrix representation of `K` on a finite-dimensional
stable subspace of its hull containing it. -/
theorem exists_not_mem_freeSet (hfin : IsLocallyFinite κ) (hweak : IsWeaklyContinuous κ)
    {x₀ : V} (hx₀ : x₀ ≠ 0) :
    ∃ (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ), Continuous τ ∧
      x₀ ∉ freeSet π hfin hweak τ := by
  classical
  obtain ⟨E, hE, hx₀E, hEs⟩ := hfin x₀
  let E₀ : Submodule ℂ V := E ⊓ hull κ π x₀
  have hE₀s : ∀ (k : K), ∀ y ∈ E₀, κ k y ∈ E₀ := fun k y hy =>
    ⟨hEs k y hy.1, (hull_isStable κ π x₀).1 k y hy.2⟩
  have : FiniteDimensional ℂ E₀ := Submodule.finiteDimensional_of_le inf_le_left
  let ρ₀ := restrictRep κ E₀ hE₀s
  let b := Module.finBasis ℂ E₀
  let d := Module.finrank ℂ E₀
  let A : Module.End ℂ E₀ →* Matrix (Fin d) (Fin d) ℂ :=
    (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom
  let τ : K →* Matrix (Fin d) (Fin d) ℂ := A.comp ρ₀
  have hτ : ∀ k, τ k = LinearMap.toMatrix b b (ρ₀ k) := fun k => rfl
  have hτc : Continuous τ := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have h : ∀ k, τ k i j = b.coord i (ρ₀ k (b j)) := fun k => by
      rw [hτ, LinearMap.toMatrix_apply, Module.Basis.coord_apply]
    simp_rw [h]
    exact isWeaklyContinuous_restrict hweak hE₀s (b.coord i) (b j)
  refine ⟨d, τ, hτc, fun hfree => ?_⟩
  let T₀ : (Fin d → ℂ) →ₗ[ℂ] V := E₀.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hT₀ : T₀ ∈ intertwiners κ (hull κ π x₀) d τ := by
    refine ⟨fun y => (b.equivFun.symm y).2.2, fun k y => ?_⟩
    change ((b.equivFun.symm (τ k *ᵥ y) : E₀) : V) = κ k (b.equivFun.symm y : E₀)
    obtain ⟨z, rfl⟩ := b.equivFun.surjective y
    rw [hτ, LinearEquiv.symm_apply_apply, Module.Basis.equivFun_apply,
      LinearMap.toMatrix_mulVec_repr, ← Module.Basis.equivFun_apply,
      LinearEquiv.symm_apply_apply]
    rfl
  rw [mem_freeSet] at hfree
  rw [hfree, Submodule.mem_bot] at hT₀
  have h1 : T₀ (b.equivFun ⟨x₀, hx₀E, mem_hull κ π x₀⟩) = x₀ := by
    change ((b.equivFun.symm (b.equivFun ⟨x₀, hx₀E, mem_hull κ π x₀⟩) : E₀) : V) = x₀
    rw [LinearEquiv.symm_apply_apply]
  rw [hT₀, LinearMap.zero_apply] at h1
  exact hx₀ h1.symm

/-- **Detection.** If the free set is zero, every nonzero stable subspace has a nonzero
`τ`-intertwiner. -/
theorem intertwiners_ne_bot_of_freeSet_eq_bot {hfin : IsLocallyFinite κ}
    {hweak : IsWeaklyContinuous κ} {d : ℕ} {τ : K →* Matrix (Fin d) (Fin d) ℂ}
    (h : freeSet π hfin hweak τ = ⊥) {W : Submodule ℂ V} (hWs : IsStable κ π W)
    (hW : W ≠ ⊥) : intertwiners κ W d τ ≠ ⊥ := by
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  intro hfree
  apply hx0
  have : x ∈ freeSet π hfin hweak τ := free_mono κ (hull_le κ π hWs hxW) τ hfree
  rw [h, Submodule.mem_bot] at this
  exact this

end Langlands.Automorphic.PlaceComponent
