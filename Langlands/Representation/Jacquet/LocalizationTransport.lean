import Langlands.Representation.Jacquet.Localization

/-! Algebraic transport and a scalar vanishing criterion for character quotients. -/

noncomputable section

namespace Langlands.Jacquet.Localization

universe uR uG uH uV uW

variable {R : Type uR} [CommRing R]
variable {G : Type uG} {H : Type uH} [Group G] [Group H]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Compatible equivalences of the acting subgroups and coefficient modules
induce an equivalence of the actual character-localized quotients. -/
def transportEquiv (ρ : Representation R G V) (σ : Representation R H W)
    (U : Subgroup G) (N : Subgroup H) (θ : U →* Rˣ) (η : N →* Rˣ)
    (e : U ≃* N) (f : V ≃ₗ[R] W)
    (hρ : ∀ (u : U) (v : V), f (ρ u v) = σ (e u) (f v))
    (hθ : ∀ u : U, θ u = η (e u)) :
    Coinvariants ρ U θ ≃ₗ[R] Coinvariants σ N η := by
  let forward := lift ρ U θ (mk σ N η ∘ₗ f.toLinearMap) (fun u v => by
    change mk σ N η (f (ρ u v)) = (θ u : R) • mk σ N η (f v)
    rw [hρ, mk_apply_subgroup, hθ])
  let backward := lift σ N η (mk ρ U θ ∘ₗ f.symm.toLinearMap) (fun u v => by
    change mk ρ U θ (f.symm (σ u v)) = (η u : R) • mk ρ U θ (f.symm v)
    have h : f.symm (σ u v) = ρ (e.symm u) (f.symm v) := by
      apply f.injective
      simpa using (hρ (e.symm u) (f.symm v)).symm
    rw [h, mk_apply_subgroup, hθ]
    simp)
  refine LinearEquiv.ofLinearMap forward backward ?_ ?_
  · apply hom_ext
    ext v
    change mk σ N η (f (f.symm v)) = mk σ N η v
    rw [f.apply_symm_apply]
  · apply hom_ext
    ext v
    change mk ρ U θ (f.symm (f v)) = mk ρ U θ v
    rw [f.symm_apply_apply]

@[simp]
theorem transportEquiv_mk (ρ : Representation R G V) (σ : Representation R H W)
    (U : Subgroup G) (N : Subgroup H) (θ : U →* Rˣ) (η : N →* Rˣ)
    (e : U ≃* N) (f : V ≃ₗ[R] W)
    (hρ : ∀ (u : U) (v : V), f (ρ u v) = σ (e u) (f v))
    (hθ : ∀ u : U, θ u = η (e u)) (v : V) :
    transportEquiv ρ σ U N θ η e f hρ hθ (mk ρ U θ v) =
      mk σ N η (f v) := rfl

/-- Restricting the ambient representation to the localizing subgroup leaves
the character quotient unchanged. The map on representatives is the identity. -/
def restrictionEquiv (ρ : Representation R G V) (U : Subgroup G) (θ : U →* Rˣ) :
    Coinvariants (ρ.comp U.subtype) (⊤ : Subgroup U)
        (θ.comp (⊤ : Subgroup U).subtype) ≃ₗ[R] Coinvariants ρ U θ :=
  transportEquiv (ρ.comp U.subtype) ρ ⊤ U
    (θ.comp (⊤ : Subgroup U).subtype) θ
    Subgroup.topEquiv (LinearEquiv.refl R V) (fun _ _ => rfl) (fun _ => rfl)

@[simp]
theorem restrictionEquiv_mk (ρ : Representation R G V) (U : Subgroup G)
    (θ : U →* Rˣ) (v : V) :
    restrictionEquiv ρ U θ
      (mk (ρ.comp U.subtype) ⊤ (θ.comp (⊤ : Subgroup U).subtype) v) =
      mk ρ U θ v := rfl

/-- An equivalence of representations induces an equivalence of their
localizations at the same subgroup and character. -/
def representationEquiv {ρ : Representation R G V} {σ : Representation R G W}
    (U : Subgroup G) (θ : U →* Rˣ) (f : ρ.Equiv σ) :
    Coinvariants ρ U θ ≃ₗ[R] Coinvariants σ U θ :=
  transportEquiv ρ σ U U θ θ (MulEquiv.refl U) f.toLinearEquiv
    (fun u v => Representation.IntertwiningMap.isIntertwining ρ σ
      f.toIntertwiningMap u v) (fun _ => rfl)

@[simp]
theorem representationEquiv_mk {ρ : Representation R G V} {σ : Representation R G W}
    (U : Subgroup G) (θ : U →* Rˣ) (f : ρ.Equiv σ) (v : V) :
    representationEquiv U θ f (mk ρ U θ v) = mk σ U θ (f v) := rfl

section Field

variable {k : Type uR} [Field k]
variable [Module k V]

/-- A trivially acting element detected by the character makes the entire
localized quotient zero, without smoothness or dimension assumptions. -/
theorem subsingleton_of_trivial_action (ρ : Representation k G V)
    (U : Subgroup G) (θ : U →* kˣ) (u : U)
    (hρ : ∀ v : V, ρ u v = v) (hθ : θ u ≠ 1) :
    Subsingleton (Coinvariants ρ U θ) := by
  have hc : (1 : k) - (θ u : k) ≠ 0 := by
    intro h
    apply hθ
    apply Units.ext
    exact (sub_eq_zero.mp h).symm
  have hz : ∀ q : Coinvariants ρ U θ, q = 0 := by
    intro q
    obtain ⟨v, rfl⟩ := mk_surjective ρ U θ q
    have h := mk_apply_subgroup ρ U θ u v
    rw [hρ] at h
    have hs : ((1 : k) - (θ u : k)) • mk ρ U θ v = 0 := by
      rw [sub_smul, one_smul, sub_eq_zero]
      exact h
    exact (smul_eq_zero.mp hs).resolve_left hc
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end Field

end Langlands.Jacquet.Localization
