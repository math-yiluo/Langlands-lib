import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # A group projection from unique pinned representatives -/

noncomputable section

universe u v

namespace Langlands.PinnedQuotient

variable {Γ : Type u} {Δ : Type v} [Group Γ] [Group Δ]

/-- Supplied representative and factorization properties for a normal factor.
The relation `Pinned` labels a distinguished representative by an element
of the subgroup `B`; the geometric existence and separation are hypotheses. -/
structure SplittingData (N : Subgroup Γ) (B : Subgroup Δ)
    (Pinned : Γ → Δ → Prop) : Prop where
  one : Pinned 1 1
  mul : ∀ {g h θ ψ}, Pinned g θ → Pinned h ψ → Pinned (g * h) (θ * ψ)
  based : ∀ {g θ}, Pinned g θ → θ ∈ B
  unique : ∀ θ, θ ∈ B → ∃! g, Pinned g θ
  factor : ∀ g, ∃ θ ∈ B, ∃ s, Pinned s θ ∧ ∃ n ∈ N, g = n * s
  separate : ∀ {g θ}, Pinned g θ → g ∈ N → θ = 1

namespace SplittingData

variable {N : Subgroup Γ} {B : Subgroup Δ} {Pinned : Γ → Δ → Prop}
    (h : SplittingData N B Pinned)

/-- The unique representatives form a homomorphism. -/
def sectionHom : B →* Γ where
  toFun θ := (h.unique θ θ.property).choose
  map_one' := ((h.unique 1 B.one_mem).choose_spec.2 1 h.one).symm
  map_mul' θ ψ :=
    ((h.unique (θ * ψ) (θ * ψ).property).choose_spec.2
      ((h.unique θ θ.property).choose * (h.unique ψ ψ.property).choose)
      (h.mul (h.unique θ θ.property).choose_spec.1
        (h.unique ψ ψ.property).choose_spec.1)).symm

theorem sectionHom_pinned (θ : B) : Pinned (h.sectionHom θ) θ :=
  (h.unique θ θ.property).choose_spec.1

theorem eq_sectionHom {g : Γ} {θ : Δ} (hg : Pinned g θ) :
    g = h.sectionHom ⟨θ, h.based hg⟩ :=
  (h.unique θ (h.based hg)).choose_spec.2 g hg

variable [N.Normal]

/-- The homomorphism to the quotient induced by the representatives. -/
def quotientSection : B →* Γ ⧸ N :=
  (QuotientGroup.mk' N).comp h.sectionHom

theorem quotientSection_injective : Function.Injective h.quotientSection := by
  apply (h.quotientSection.ker_eq_bot_iff).mp
  apply le_antisymm
  · intro θ hθ
    change θ = 1
    apply Subtype.ext
    exact h.separate (h.sectionHom_pinned θ) ((QuotientGroup.eq_one_iff _).mp hθ)
  · exact bot_le

theorem quotientSection_surjective : Function.Surjective h.quotientSection := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  obtain ⟨θ, hθ, s, hs, n, hn, hg⟩ := h.factor g
  refine ⟨⟨θ, hθ⟩, ?_⟩
  change (QuotientGroup.mk' N) (h.sectionHom ⟨θ, hθ⟩) =
    (QuotientGroup.mk' N) g
  have hs' : s = h.sectionHom ⟨θ, hθ⟩ := h.eq_sectionHom hs
  have hn' : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  rw [hg, map_mul, hn', one_mul, hs']

/-- The quotient by the normal factor is the group of representative labels. -/
def quotientEquiv : B ≃* Γ ⧸ N :=
  MulEquiv.ofBijective h.quotientSection
    ⟨h.quotientSection_injective, h.quotientSection_surjective⟩

/-- The projection onto labels, viewed in their ambient group. -/
def projection : Γ →* Δ :=
  B.subtype.comp (h.quotientEquiv.symm.toMonoidHom.comp (QuotientGroup.mk' N))

@[simp]
theorem projection_sectionHom (θ : B) :
    h.projection (h.sectionHom θ) = θ := by
  change (h.quotientEquiv.symm (h.quotientEquiv θ) : Δ) = θ
  rw [MulEquiv.symm_apply_apply]

theorem projection_eq_one_iff (g : Γ) :
    h.projection g = 1 ↔ g ∈ N := by
  change (h.quotientEquiv.symm ((QuotientGroup.mk' N) g) : Δ) = 1 ↔ g ∈ N
  have hb : ∀ θ : B, (θ : Δ) = 1 ↔ θ = 1 :=
    fun θ => ⟨fun hθ => Subtype.ext hθ, fun hθ => congrArg Subtype.val hθ⟩
  rw [hb, MulEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff g

theorem projection_ker : h.projection.ker = N :=
  Subgroup.ext fun g => h.projection_eq_one_iff g

theorem mem_projection_range_iff (θ : Δ) :
    θ ∈ h.projection.range ↔ θ ∈ B := by
  constructor
  · rintro ⟨g, rfl⟩
    exact (h.quotientEquiv.symm ((QuotientGroup.mk' N) g)).property
  · intro hθ
    exact ⟨h.sectionHom ⟨θ, hθ⟩, h.projection_sectionHom ⟨θ, hθ⟩⟩

theorem projection_range : h.projection.range = B :=
  Subgroup.ext h.mem_projection_range_iff

theorem projection_pinned {g : Γ} {θ : Δ} (hg : Pinned g θ) :
    h.projection g = θ := by
  rw [h.eq_sectionHom hg, h.projection_sectionHom]

end SplittingData

end Langlands.PinnedQuotient
