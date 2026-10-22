import Langlands.ClassField.Global.Cocycle
import Langlands.GroupTheory.CocycleMap
import Mathlib.Algebra.Algebra.Tower

/-! # Restriction of actual relative idele-class cocycle extensions -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField Topology
open scoped NumberField

universe u v w

variable {K : Type u} {K' : Type v} {E : Type w}
  [Field K] [Field K'] [Field E] [NumberField E]
  [Algebra K K'] [Algebra K E] [Algebra K' E] [IsScalarTower K K' E]

attribute [local instance] relativeIdeleClassAction relativeGaloisTopology

/-- Restricting the scalar field of an automorphism leaves its arithmetic action unchanged. -/
theorem relativeIdeleClassAut_restrictScalars (σ : E ≃ₐ[K'] E)
    (a : IdeleClassGroup (𝓞 E) E) :
    relativeIdeleClassAut K E (σ.restrictScalars K) a =
      relativeIdeleClassAut K' E σ a := rfl

namespace RelativeIdeleCocycle

variable (K') (c : RelativeIdeleCocycle K E)

/-- Pull a relative cocycle back along `Gal(E/K') → Gal(E/K)` in a scalar tower. -/
def restrictBase : RelativeIdeleCocycle K' E where
  toFun p := c (p.1.restrictScalars K, p.2.restrictScalars K)
  cocycle σ τ υ := c.cocycle (σ.restrictScalars K) (τ.restrictScalars K)
    (υ.restrictScalars K)
  normalized := c.normalized

@[simp] theorem restrictBase_apply (σ τ : E ≃ₐ[K'] E) :
    restrictBase K' c (σ, τ) = c (σ.restrictScalars K, τ.restrictScalars K) := rfl

/-- The restriction inclusion uses identity coefficients and the constant-one cochain. -/
def restrictionMapData :
    NormalizedTwoCocycle.MapData (restrictBase K' c) c
      (MonoidHom.id _) (AlgEquiv.restrictScalarsHom K) where
  cochain _ := 1
  equivariant _ _ := rfl
  compatible σ τ := by
    change c (σ.restrictScalars K, τ.restrictScalars K) * 1 =
      1 * ((σ.restrictScalars K) • (1 : IdeleClassGroup (𝓞 E) E)) *
        c (σ.restrictScalars K, τ.restrictScalars K)
    rw [smul_one]
    exact (mul_one _).trans
      ((congrArg (fun a : IdeleClassGroup (𝓞 E) E =>
          a * c (σ.restrictScalars K, τ.restrictScalars K)) (one_mul 1)).trans
        (one_mul _)).symm

/-- The constructed inclusion of the restricted relative extension. -/
def restrictionInclusion : (restrictBase K' c).Extension →* c.Extension :=
  (restrictionMapData K' c).toMonoidHom

@[simp] theorem restrictionInclusion_left (x : (restrictBase K' c).Extension) :
    (restrictionInclusion K' c x).left = x.left := by
  change x.left * 1 = x.left
  exact mul_one x.left

@[simp] theorem restrictionInclusion_right (x : (restrictBase K' c).Extension) :
    (restrictionInclusion K' c x).right = x.right.restrictScalars K := rfl

@[simp] theorem restrictionInclusion_inclusion (a : IdeleClassGroup (𝓞 E) E) :
    restrictionInclusion K' c (inclusion (restrictBase K' c) a) = inclusion c a :=
  (restrictionMapData K' c).toMonoidHom_inl a

@[simp] theorem projection_restrictionInclusion (x : (restrictBase K' c).Extension) :
    projection c (restrictionInclusion K' c x) =
      (projection (restrictBase K' c) x).restrictScalars K := rfl

@[simp] theorem restrictionInclusion_sectionMap (σ : E ≃ₐ[K'] E) :
    restrictionInclusion K' c (sectionMap (restrictBase K' c) σ) =
      sectionMap c (σ.restrictScalars K) := by
  apply NormalizedTwoCocycle.Extension.ext <;> simp

theorem restrictionInclusion_injective : Function.Injective (restrictionInclusion K' c) :=
  (restrictionMapData K' c).injective Function.injective_id
    (AlgEquiv.restrictScalarsHom_injective K)

/-- The image is exactly the inverse image of the actual subgroup of automorphisms
that are linear over the larger base field. -/
theorem range_restrictionInclusion :
    (restrictionInclusion K' c).range =
      ((AlgEquiv.restrictScalarsHom K : (E ≃ₐ[K'] E) →* (E ≃ₐ[K] E)).range).comap
        (projection c) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.right, rfl⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨⟨x.left, σ⟩, ?_⟩
    apply NormalizedTwoCocycle.Extension.ext
    · simp
    · exact hσ

theorem continuous_restrictionInclusion : Continuous (restrictionInclusion K' c) :=
  (restrictionMapData K' c).continuous continuous_id continuous_of_discreteTopology
    continuous_const

/-- The restricted extension embeds with its existing product topology as an open subgroup. -/
theorem isOpenEmbedding_restrictionInclusion : IsOpenEmbedding (restrictionInclusion K' c) := by
  have hσ : IsOpenEmbedding
      (AlgEquiv.restrictScalarsHom K : (E ≃ₐ[K'] E) →* (E ≃ₐ[K] E)) :=
    .of_continuous_injective_isOpenMap continuous_of_discreteTopology
      (AlgEquiv.restrictScalarsHom_injective K) (fun _ _ => isOpen_discrete _)
  have h := (NormalizedTwoCocycle.Extension.homeomorphProd c).symm.isOpenEmbedding.comp
    ((IsOpenEmbedding.id.prodMap hσ).comp
      (NormalizedTwoCocycle.Extension.homeomorphProd (restrictBase K' c)).isOpenEmbedding)
  convert h using 1
  funext x
  apply NormalizedTwoCocycle.Extension.ext
  · exact restrictionInclusion_left K' c x
  · rfl

/-- Continuous bundled form of the same arithmetic restriction inclusion. -/
def restrictionContinuousInclusion : (restrictBase K' c).Extension →ₜ* c.Extension where
  __ := restrictionInclusion K' c
  continuous_toFun := continuous_restrictionInclusion K' c

end RelativeIdeleCocycle
end Langlands.ClassField.Global
