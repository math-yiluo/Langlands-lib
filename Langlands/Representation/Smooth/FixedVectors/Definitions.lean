import Langlands.Representation.Smooth.Definitions

/-! Algebraic restriction of intertwiners and equivalences to fixed vectors. -/

noncomputable section

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable {ρ : Representation R G V} {σ : Representation R G W}

/-- Restrict an intertwiner to the vectors fixed by the same subgroup. -/
def fixedVectorsMap (f : ρ.IntertwiningMap σ) (K : Subgroup G) :
    fixedVectors ρ K →ₗ[R] fixedVectors σ K :=
  (f.toLinearMap.comp (fixedVectors ρ K).subtype).codRestrict
    (fixedVectors σ K) (by
      intro v
      change ∀ k : K, σ (k : G) (f (v : V)) = f (v : V)
      intro k
      rw [← f.isIntertwining]
      exact congrArg f (v.property k))

/-- Restrict a representation equivalence and its inverse to fixed vectors. -/
def fixedVectorsEquiv (e : ρ.Equiv σ) (K : Subgroup G) :
    fixedVectors ρ K ≃ₗ[R] fixedVectors σ K where
  toLinearMap := fixedVectorsMap e.toIntertwiningMap K
  invFun := fixedVectorsMap e.symm.toIntertwiningMap K
  left_inv v := by
    apply Subtype.ext
    exact e.symm_apply_apply v
  right_inv w := by
    apply Subtype.ext
    exact e.apply_symm_apply w

end Langlands
