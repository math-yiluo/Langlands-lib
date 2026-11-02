import Langlands.Representation.Jacquet.Localization

/-!
# Canonical maps for nested character-localized quotients

The map sends the class of `v` to the class of the same `v`. Characters must
agree on the smaller subgroup. Equivariance uses a common normalizing subgroup.
-/

noncomputable section

set_option maxHeartbeats 1600000

open CategoryTheory

namespace Langlands.Jacquet.Localization

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

section Linear

variable (U N : Subgroup G) (hUN : U ≤ N)
variable (θ : U →* Rˣ) (η : N →* Rˣ)
variable (hθη : ∀ u : U, η (Subgroup.inclusion hUN u) = θ u)

/-- The quotient-induced map `[v]_(U,θ) ↦ [v]_(N,η)`. -/
def transitionLinear (ρ : Representation R G V) :
    Coinvariants ρ U θ →ₗ[R] Coinvariants ρ N η :=
  lift ρ U θ (mk ρ N η) fun u v => by
    rw [← hθη u]
    exact mk_apply_subgroup ρ N η (Subgroup.inclusion hUN u) v

@[simp]
theorem transitionLinear_mk (ρ : Representation R G V) (v : V) :
    transitionLinear U N hUN θ η hθη ρ (mk ρ U θ v) = mk ρ N η v := rfl

/-- The defining square with the two canonical quotient maps. -/
theorem transitionLinear_comp_mk (ρ : Representation R G V) :
    transitionLinear U N hUN θ η hθη ρ ∘ₗ mk ρ U θ = mk ρ N η := rfl

/-- The representative formula determines the transition uniquely. -/
theorem transitionLinear_unique (ρ : Representation R G V)
    (f : Coinvariants ρ U θ →ₗ[R] Coinvariants ρ N η)
    (hf : f ∘ₗ mk ρ U θ = mk ρ N η) :
    f = transitionLinear U N hUN θ η hθη ρ := hom_ext hf

theorem transitionLinear_surjective (ρ : Representation R G V) :
    Function.Surjective (transitionLinear U N hUN θ η hθη ρ) := by
  intro x
  obtain ⟨v, rfl⟩ := mk_surjective ρ N η x
  exact ⟨mk ρ U θ v, rfl⟩

/-- Naturality is an equality of the actual induced quotient maps. -/
theorem transitionLinear_natural {ρ : Representation R G V} {σ : Representation R G W}
    (f : ρ.IntertwiningMap σ) :
    transitionLinear U N hUN θ η hθη σ ∘ₗ mapLinear U θ f =
      mapLinear N η f ∘ₗ transitionLinear U N hUN θ η hθη ρ :=
  hom_ext rfl

end Linear

@[simp]
theorem transitionLinear_refl (U : Subgroup G) (θ : U →* Rˣ)
    (ρ : Representation R G V) :
    transitionLinear U U le_rfl θ θ (fun _ => rfl) ρ = LinearMap.id :=
  hom_ext rfl

/-- Transitions along a chain of subgroups compose on the nose. -/
theorem transitionLinear_comp (U N P : Subgroup G) (hUN : U ≤ N) (hNP : N ≤ P)
    (θ : U →* Rˣ) (η : N →* Rˣ) (ζ : P →* Rˣ)
    (hθη : ∀ u : U, η (Subgroup.inclusion hUN u) = θ u)
    (hηζ : ∀ n : N, ζ (Subgroup.inclusion hNP n) = η n)
    (ρ : Representation R G V) :
    transitionLinear N P hNP η ζ hηζ ρ ∘ₗ transitionLinear U N hUN θ η hθη ρ =
      transitionLinear U P (hUN.trans hNP) θ ζ
        (fun u => (hηζ (Subgroup.inclusion hUN u)).trans (hθη u)) ρ :=
  hom_ext rfl

section Equivariant

variable (U N : Subgroup G) (hUN : U ≤ N)
variable (θ : U →* Rˣ) (η : N →* Rˣ)
variable (hθη : ∀ u : U, η (Subgroup.inclusion hUN u) = θ u)
variable (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)
variable (hMN : M ≤ Subgroup.normalizer N)
variable (hθ : IsInvariant U M hMU θ) (hη : IsInvariant N M hMN η)

/-- The quotient-induced transition, equivariant for the common normalizer. -/
def transition (ρ : Representation R G V) :
    (action ρ U θ M hMU hθ).IntertwiningMap (action ρ N η M hMN hη) where
  toLinearMap := transitionLinear U N hUN θ η hθη ρ
  isIntertwining' _ := hom_ext rfl

@[simp]
theorem transition_mk (ρ : Representation R G V) (v : V) :
    transition U N hUN θ η hθη M hMU hMN hθ hη ρ (mk ρ U θ v) =
      mk ρ N η v := rfl

/-- The transition commutes with the original canonical equivariant quotient maps. -/
theorem transition_comp_quotientMap (ρ : Representation R G V) :
    (transition U N hUN θ η hθη M hMU hMN hθ hη ρ).comp
        (quotientMap ρ U θ M hMU hθ) =
      quotientMap ρ N η M hMN hη := by
  ext v
  rfl

theorem transition_natural {ρ : Representation R G V} {σ : Representation R G W}
    (f : ρ.IntertwiningMap σ) :
    (transition U N hUN θ η hθη M hMU hMN hθ hη σ).comp
        (map U θ M hMU hθ f) =
      (map N η M hMN hη f).comp
        (transition U N hUN θ η hθη M hMU hMN hθ hη ρ) := by
  apply Representation.IntertwiningMap.ext
  exact hom_ext rfl

section Smooth

variable [TopologicalSpace G]

/-- The canonical natural transformation between the existing smooth functors. -/
def smoothTransition :
    smoothFunctor.{uR, uG, uV} U θ M hMU hθ ⟶
      smoothFunctor N η M hMN hη where
  app A := SmoothRep.ofHom
    (transition U N hUN θ η hθη M hMU hMN hθ hη A.representation)
  naturality {A B} f := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    exact transition_natural U N hUN θ η hθη M hMU hMN hθ hη (SmoothRep.hom f)

@[simp]
theorem smoothTransition_app_mk (A : SmoothRep.{uR, uG, uV} R G) (v : A) :
    SmoothRep.hom ((smoothTransition U N hUN θ η hθη M hMU hMN hθ hη).app A)
        (mk A.representation U θ v) =
      mk A.representation N η v := rfl

end Smooth

end Equivariant

end Langlands.Jacquet.Localization
