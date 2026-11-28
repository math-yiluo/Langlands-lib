import Langlands.GroupTheory.CocycleExtension
import Mathlib.Algebra.GroupWithZero.Action.End

/-! # Normalized two-cocycles for central extensions -/

namespace Langlands

universe u v w x

/-- The trivial action, obtained by restricting the tautological action of `MulAut`. -/
abbrev trivialCoefficientAction (G : Type u) (A : Type v) [Group G] [CommGroup A] :
    MulDistribMulAction G A :=
  MulDistribMulAction.compHom A (1 : G →* MulAut A)

/-- A normalized two-cocycle whose coefficient action is trivial. -/
abbrev CentralTwoCocycle (G : Type u) (A : Type v) [Group G] [CommGroup A] :=
  @NormalizedTwoCocycle G A _ _ (trivialCoefficientAction G A)

namespace CentralTwoCocycle

attribute [local instance] trivialCoefficientAction

variable {G : Type u} {A : Type v} {H : Type w} {B : Type x}
  [Group G] [CommGroup A] [Group H] [CommGroup B]

/-- The cocycle identity in central coordinates. -/
theorem identity (σ : CentralTwoCocycle G A) (g h j : G) :
    σ (g * h, j) * σ (g, h) = σ (h, j) * σ (g, h * j) :=
  σ.cocycle g h j

/-- Pullback along a group homomorphism. -/
def pullback (σ : CentralTwoCocycle H A) (f : G →* H) : CentralTwoCocycle G A where
  toFun p := σ (f p.1, f p.2)
  cocycle g h j := by
    change σ (f (g * h), f j) * σ (f g, f h) = σ (f h, f j) * σ (f g, f (h * j))
    simpa only [map_mul] using σ.identity (f g) (f h) (f j)
  normalized := by simp

/-- Postcomposition by a homomorphism of coefficient groups. -/
def map (σ : CentralTwoCocycle G A) (f : A →* B) : CentralTwoCocycle G B where
  toFun p := f (σ p)
  cocycle g h j := by
    change f (σ (g * h, j)) * f (σ (g, h)) = f (σ (h, j)) * f (σ (g, h * j))
    simpa only [map_mul] using congrArg f (σ.identity g h j)
  normalized := by simp [σ.normalized]

/-- The product of two normalized cocycles in the same central coordinates. -/
def pointwiseMul (σ τ : CentralTwoCocycle G A) : CentralTwoCocycle G A where
  toFun p := σ p * τ p
  cocycle g h j := by
    change (σ (g * h, j) * τ (g * h, j)) * (σ (g, h) * τ (g, h)) =
      (σ (h, j) * τ (h, j)) * (σ (g, h * j) * τ (g, h * j))
    calc
      _ = (σ (g * h, j) * σ (g, h)) * (τ (g * h, j) * τ (g, h)) := by ac_rfl
      _ = (σ (h, j) * σ (g, h * j)) * (τ (h, j) * τ (g, h * j)) := by
        rw [σ.identity, τ.identity]
      _ = _ := by ac_rfl
  normalized := by simp [σ.normalized, τ.normalized]

/-- A multiplicative pairing in two variables is a normalized two-cocycle. -/
def ofBilinear (b : G →* G →* A) : CentralTwoCocycle G A where
  toFun p := b p.1 p.2
  cocycle g h j := by
    change b (g * h) j * b g h = b h j * b g (h * j)
    rw [map_mul, MonoidHom.mul_apply, map_mul, mul_assoc, mul_comm (b g h),
      mul_left_comm (b g j)]
  normalized := by simp

@[simp]
theorem pullback_apply (σ : CentralTwoCocycle H A) (f : G →* H) (g h : G) :
    σ.pullback f (g, h) = σ (f g, f h) := rfl

@[simp]
theorem map_apply (σ : CentralTwoCocycle G A) (f : A →* B) (g h : G) :
    σ.map f (g, h) = f (σ (g, h)) := rfl

@[simp]
theorem pointwiseMul_apply (σ τ : CentralTwoCocycle G A) (g h : G) :
    σ.pointwiseMul τ (g, h) = σ (g, h) * τ (g, h) := rfl

@[simp]
theorem ofBilinear_apply (b : G →* G →* A) (g h : G) :
    ofBilinear b (g, h) = b g h := rfl

/-- The included coefficients are central in the existing cocycle extension. -/
theorem inl_mem_center (σ : CentralTwoCocycle G A) (a : A) :
    NormalizedTwoCocycle.Extension.inl σ a ∈ Subgroup.center σ.Extension := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  rw [NormalizedTwoCocycle.Extension.mul_inl]
  rfl

end CentralTwoCocycle
end Langlands
