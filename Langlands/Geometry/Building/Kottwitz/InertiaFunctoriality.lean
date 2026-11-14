import Langlands.Geometry.Building.Kottwitz.InertiaCoinvariants

/-! # Functoriality of inertia coinvariants and their residual action -/

noncomputable section

universe u v w z

namespace Langlands.Geometry.Building.Kottwitz

variable (k K E : Type u) [Field k] [Field K] [Field E]
  [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
  [Normal k K]
  {V : Type v} {W : Type w} {U : Type z}
  [AddCommGroup V] [Module ℤ V] [AddCommGroup W] [Module ℤ W]
  [AddCommGroup U] [Module ℤ U]
  {ρ : Representation ℤ (E ≃ₐ[k] E) V}
  {τ : Representation ℤ (E ≃ₐ[k] E) W}
  {υ : Representation ℤ (E ≃ₐ[k] E) U}

/-- Descent of an absolute Galois intertwiner to the actual inertia quotients. -/
def inertiaMap (f : ρ.IntertwiningMap τ) :
    inertiaCoinvariants k K E ρ →ₗ[ℤ] inertiaCoinvariants k K E τ :=
  Representation.Coinvariants.map _ _
    { toLinearMap := f.toLinearMap
      isIntertwining' σ := f.isIntertwining' σ.val }

@[simp] theorem inertiaMap_projection (f : ρ.IntertwiningMap τ) (x : V) :
    inertiaMap k K E f (inertiaProjection k K E ρ x) =
      inertiaProjection k K E τ (f x) := rfl

/-- The representative law determines a linear map from inertia coinvariants. -/
theorem inertiaMap_unique (f : ρ.IntertwiningMap τ)
    (m : inertiaCoinvariants k K E ρ →ₗ[ℤ] inertiaCoinvariants k K E τ)
    (hm : ∀ x, m (inertiaProjection k K E ρ x) =
      inertiaProjection k K E τ (f x)) :
    m = inertiaMap k K E f := by
  apply Representation.Coinvariants.hom_ext
  exact LinearMap.ext hm

/-- Every absolute intertwiner has a unique descent specified on representatives. -/
theorem inertiaMap_existsUnique (f : ρ.IntertwiningMap τ) :
    ∃! m : inertiaCoinvariants k K E ρ →ₗ[ℤ] inertiaCoinvariants k K E τ,
      ∀ x, m (inertiaProjection k K E ρ x) =
        inertiaProjection k K E τ (f x) :=
  ⟨inertiaMap k K E f, fun _ => rfl, fun m hm => inertiaMap_unique k K E f m hm⟩

@[simp] theorem inertiaMap_id :
    inertiaMap k K E (Representation.IntertwiningMap.id ρ) = LinearMap.id := by
  apply Representation.Coinvariants.hom_ext
  rfl

@[simp] theorem inertiaMap_comp (f : ρ.IntertwiningMap τ) (g : τ.IntertwiningMap υ) :
    (inertiaMap k K E g).comp (inertiaMap k K E f) =
      inertiaMap k K E (g.comp f) := by
  apply Representation.Coinvariants.hom_ext
  rfl

/-- An absolute Galois equivalence descends with its inverse to inertia coinvariants. -/
def inertiaEquiv (e : ρ.Equiv τ) :
    inertiaCoinvariants k K E ρ ≃ₗ[ℤ] inertiaCoinvariants k K E τ :=
  LinearEquiv.ofLinearMap
    (inertiaMap k K E e.toIntertwiningMap)
    (inertiaMap k K E e.symm.toIntertwiningMap)
    (by
      apply Representation.Coinvariants.hom_ext
      ext x
      change inertiaProjection k K E τ (e (e.symm x)) =
        inertiaProjection k K E τ x
      rw [e.apply_symm_apply])
    (by
      apply Representation.Coinvariants.hom_ext
      ext x
      change inertiaProjection k K E ρ (e.symm (e x)) =
        inertiaProjection k K E ρ x
      rw [e.symm_apply_apply])

@[simp] theorem inertiaEquiv_projection (e : ρ.Equiv τ) (x : V) :
    inertiaEquiv k K E e (inertiaProjection k K E ρ x) =
      inertiaProjection k K E τ (e x) := rfl

variable [Normal k E]

/-- The descended map commutes with the actual residual group `Aut_k(K)`. -/
theorem inertiaMap_equivariant (f : ρ.IntertwiningMap τ)
    (σ : K ≃ₐ[k] K) (x : inertiaCoinvariants k K E ρ) :
    inertiaMap k K E f (inertiaGammaRepresentation k K E ρ σ x) =
      inertiaGammaRepresentation k K E τ σ (inertiaMap k K E f x) := by
  obtain ⟨γ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := k) (E := E) (K₁ := K) σ
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective
    (ρ.comp (relativeInertia k K E).subtype) x
  change inertiaMap k K E f
    (inertiaGammaRepresentation k K E ρ (γ.restrictNormal K)
      (inertiaProjection k K E ρ v)) =
    inertiaGammaRepresentation k K E τ (γ.restrictNormal K)
      (inertiaMap k K E f (inertiaProjection k K E ρ v))
  rw [inertiaGammaRepresentation_restrict, inertiaMap_projection,
    inertiaMap_projection, inertiaGammaRepresentation_restrict]
  exact congrArg (inertiaProjection k K E τ)
    (congrArg (fun p : V →ₗ[ℤ] W => p v) (f.isIntertwining' γ))

/-- Inertia descent preserves equivalences as residual Galois representations. -/
def inertiaRepresentationEquiv (e : ρ.Equiv τ) :
    (inertiaGammaRepresentation k K E ρ).Equiv
      (inertiaGammaRepresentation k K E τ) :=
  Representation.Equiv.mk (inertiaEquiv k K E e) fun σ =>
    LinearMap.ext (inertiaMap_equivariant k K E e.toIntertwiningMap σ)

end Langlands.Geometry.Building.Kottwitz
