import Langlands.Representation.Induction.Definitions

/-! Smooth induction transported between different topological groups. -/

noncomputable section

namespace Langlands.Induction

universe uR uG uH uV

variable {R : Type uR} {G : Type uG} {H : Type uH} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [AddCommGroup V] [Module R V]
variable {P : Subgroup G} {Q : Subgroup H}
variable {σ : Representation R P V} {τ : Representation R Q V}

/-- Precomposition transports covariance and a uniform open right stabilizer. -/
def precomposeSmoothGroupFunction (θ : H ≃ₜ* G) (e : Q ≃* P)
    (he : ∀ q : Q, (e q : G) = θ (q : H)) (hστ : ∀ q : Q, σ (e q) = τ q)
    (f : SmoothFunctions P σ) : SmoothFunctions Q τ :=
  ⟨⟨fun x => eval P σ f (θ x), by
    intro q x
    change eval P σ f (θ ((q : H) * x)) = τ q (eval P σ f (θ x))
    rw [map_mul, ← he q]
    exact (f.1.2 (e q) (θ x)).trans
      (congrArg (fun A : Module.End R V => A (eval P σ f (θ x))) (hστ q))⟩, by
    obtain ⟨K, hK⟩ := f.property
    refine ⟨K.comap θ.toMonoidHom θ.continuous, ?_⟩
    intro k
    apply Subtype.ext
    funext x
    change eval P σ f (θ (x * (k : H))) = eval P σ f (θ x)
    rw [map_mul]
    exact congrArg (fun φ : EquivariantFunctions P σ => φ.1 (θ x))
      (hK ⟨θ (k : H), k.property⟩)⟩

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
private theorem precomposeGroup_symm_subgroup (θ : H ≃ₜ* G) (e : Q ≃* P)
    (he : ∀ q : Q, (e q : G) = θ (q : H)) (p : P) :
    (e.symm p : H) = θ.symm (p : G) := by
  apply θ.injective
  rw [← he, e.apply_symm_apply, θ.apply_symm_apply]

omit [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace H] [IsTopologicalGroup H] in
private theorem precomposeGroup_symm_rep (e : Q ≃* P)
    (hστ : ∀ q : Q, σ (e q) = τ q) (p : P) : τ (e.symm p) = σ p := by
  rw [← hστ, e.apply_symm_apply]

/-- Pulling back the ambient action identifies actual smooth induction on two groups. -/
def precomposeSmoothInducedGroupEquiv (θ : H ≃ₜ* G) (e : Q ≃* P)
    (he : ∀ q : Q, (e q : G) = θ (q : H)) (hστ : ∀ q : Q, σ (e q) = τ q) :
    Representation.Equiv ((smoothInduced P σ).comp θ.toMonoidHom) (smoothInduced Q τ) where
  toFun := precomposeSmoothGroupFunction θ e he hστ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := precomposeSmoothGroupFunction θ.symm e.symm
    (precomposeGroup_symm_subgroup θ e he) (precomposeGroup_symm_rep e hστ)
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change eval P σ f (θ (θ.symm x)) = eval P σ f x
    rw [θ.apply_symm_apply]
  right_inv h := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change eval Q τ h (θ.symm (θ x)) = eval Q τ h x
    rw [θ.symm_apply_apply]
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change eval P σ f (θ x * θ g) = eval P σ f (θ (x * g))
    rw [map_mul]

@[simp] theorem precomposeSmoothInducedGroupEquiv_eval (θ : H ≃ₜ* G) (e : Q ≃* P)
    (he : ∀ q : Q, (e q : G) = θ (q : H)) (hστ : ∀ q : Q, σ (e q) = τ q)
    (f : SmoothFunctions P σ) (x : H) :
    eval Q τ (precomposeSmoothInducedGroupEquiv θ e he hστ f) x =
      eval P σ f (θ x) := rfl

@[simp] theorem precomposeSmoothInducedGroupEquiv_symm_eval
    (θ : H ≃ₜ* G) (e : Q ≃* P)
    (he : ∀ q : Q, (e q : G) = θ (q : H)) (hστ : ∀ q : Q, σ (e q) = τ q)
    (h : SmoothFunctions Q τ) (x : G) :
    eval P σ ((precomposeSmoothInducedGroupEquiv θ e he hστ).symm h) x =
      eval Q τ h (θ.symm x) := rfl

end Langlands.Induction
