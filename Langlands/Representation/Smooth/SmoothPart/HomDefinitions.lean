import Langlands.Representation.Smooth.SmoothPart.Definitions

/-! # Linear factorization through the smooth part -/

noncomputable section

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable {ρ : Representation R G V}

/-- Maps from a smooth representation into an arbitrary representation are
linearly equivalent to maps into its smooth part. -/
def smoothHomEquiv (hρ : IsSmooth ρ) (σ : Representation R G W) :
    (ρ.IntertwiningMap σ) ≃ₗ[R] (ρ.IntertwiningMap (smoothPart σ)) where
  toFun := smoothLift hρ
  invFun f := (smoothInclusion σ).comp f
  left_inv f := by
    ext v
    rfl
  right_inv f := by
    ext v
    rfl
  map_add' f g := by
    ext v
    rfl
  map_smul' a f := by
    ext v
    rfl

end Langlands
