import Langlands.Global.AdelicFunctoriality.Isomorphism
import Langlands.GroupTheory.CocycleExtension

/-! # Cocycle extensions of relative number-field automorphisms by idele classes -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField Topology
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

universe u v

variable (K : Type u) (E : Type v) [Field K] [Field E]
  [NumberField E] [Algebra K E]

/-- The relative automorphism action on the actual idele-class group. -/
def relativeIdeleClassAut :
    (E ≃ₐ[K] E) →* (IdeleClassGroup (𝓞 E) E ≃* IdeleClassGroup (𝓞 E) E) where
  toFun σ := (ideleClassEquiv σ.toRingEquiv).toMulEquiv
  map_one' := congrArg ContinuousMulEquiv.toMulEquiv ideleClassEquiv_refl
  map_mul' σ τ := congrArg ContinuousMulEquiv.toMulEquiv
    (ideleClassEquiv_trans τ.toRingEquiv σ.toRingEquiv)

theorem continuous_relativeIdeleClassAut (σ : E ≃ₐ[K] E) :
    Continuous (relativeIdeleClassAut K E σ) :=
  (ideleClassEquiv σ.toRingEquiv).continuous

/-- The relative action is installed explicitly when constructing cocycles. -/
@[instance_reducible]
def relativeIdeleClassAction :
    MulDistribMulAction (E ≃ₐ[K] E) (IdeleClassGroup (𝓞 E) E) where
  __ := MulAction.compHom (IdeleClassGroup (𝓞 E) E) (relativeIdeleClassAut K E)
  smul_one σ := map_one (relativeIdeleClassAut K E σ)
  smul_mul σ a b := map_mul (relativeIdeleClassAut K E σ) a b

attribute [local instance] relativeIdeleClassAction

@[simp] theorem relativeIdeleClass_smul_mk (σ : E ≃ₐ[K] E) (a : IdeleGroup (𝓞 E) E) :
    σ • (QuotientGroup.mk a : IdeleClassGroup (𝓞 E) E) =
      QuotientGroup.mk (ideleEquiv σ.toRingEquiv a) := rfl

/-- The explicitly chosen discrete topology on the relative automorphism group. -/
@[instance_reducible]
def relativeGaloisTopology : TopologicalSpace (E ≃ₐ[K] E) := ⊥

attribute [local instance] relativeGaloisTopology

instance relativeGaloisDiscreteTopology : DiscreteTopology (E ≃ₐ[K] E) :=
  ⟨rfl⟩

instance relativeIdeleClassContinuousSMul :
    ContinuousSMul (E ≃ₐ[K] E) (IdeleClassGroup (𝓞 E) E) where
  continuous_smul := continuous_prod_of_discrete_left.mpr
    (continuous_relativeIdeleClassAut K E)

/-- An actual normalized cocycle for the arithmetic relative action. -/
abbrev RelativeIdeleCocycle :=
  NormalizedTwoCocycle (E ≃ₐ[K] E) (IdeleClassGroup (𝓞 E) E)

namespace RelativeIdeleCocycle

variable {K E} (c : RelativeIdeleCocycle K E)

/-- The extension built from the given arithmetic cocycle, prior to fundamental-class selection. -/
abbrev Extension := NormalizedTwoCocycle.Extension c

theorem continuous_cocycle : Continuous c :=
  continuous_of_discreteTopology

instance extensionIsTopologicalGroup : IsTopologicalGroup (Extension c) :=
  NormalizedTwoCocycle.Extension.topologicalGroup c (continuous_cocycle c)

/-- The coefficient homomorphism from the genuine idele-class quotient. -/
abbrev inclusion : IdeleClassGroup (𝓞 E) E →* Extension c :=
  NormalizedTwoCocycle.Extension.inl c

/-- The projection to the actual relative field automorphisms. -/
abbrev projection : Extension c →* (E ≃ₐ[K] E) :=
  NormalizedTwoCocycle.Extension.projection c

/-- The distinguished continuous set-theoretic section. -/
abbrev sectionMap : (E ≃ₐ[K] E) → Extension c :=
  NormalizedTwoCocycle.Extension.sectionMap c

theorem inclusion_injective : Function.Injective (inclusion c) :=
  NormalizedTwoCocycle.Extension.inl_injective c

theorem projection_surjective : Function.Surjective (projection c) :=
  NormalizedTwoCocycle.Extension.projection_surjective c

theorem exact : (inclusion c).range = (projection c).ker :=
  NormalizedTwoCocycle.Extension.range_inl_eq_ker_projection c

theorem continuous_inclusion : Continuous (inclusion c) :=
  NormalizedTwoCocycle.Extension.continuous_inl c

theorem continuous_projection : Continuous (projection c) :=
  NormalizedTwoCocycle.Extension.continuous_projection c

theorem continuous_sectionMap : Continuous (sectionMap c) :=
  NormalizedTwoCocycle.Extension.continuous_sectionMap c

theorem isOpenMap_projection : IsOpenMap (projection c) :=
  isOpenMap_snd.comp (NormalizedTwoCocycle.Extension.homeomorphProd c).isOpenMap

theorem isOpenQuotientMap_projection : IsOpenQuotientMap (projection c) :=
  ⟨projection_surjective c, continuous_projection c, isOpenMap_projection c⟩

theorem isOpenEmbedding_inclusion : IsOpenEmbedding (inclusion c) where
  toIsEmbedding :=
    (NormalizedTwoCocycle.Extension.homeomorphProd c).symm.isEmbedding.comp
      (isEmbedding_prodMkLeft (1 : E ≃ₐ[K] E))
  isOpen_range := by
    have h : Set.range (inclusion c) = (projection c) ⁻¹' {1} := by
      ext x
      change x ∈ (inclusion c).range ↔ x ∈ (projection c).ker
      rw [exact c]
    rw [h]
    exact (isOpen_discrete {1}).preimage (continuous_projection c)

theorem factorSet (σ τ : E ≃ₐ[K] E) :
    sectionMap c σ * sectionMap c τ * (sectionMap c (σ * τ))⁻¹ =
      inclusion c (c (σ, τ)) :=
  NormalizedTwoCocycle.Extension.sectionMap_factorSet c σ τ

theorem conjugation (x : Extension c) (a : IdeleClassGroup (𝓞 E) E) :
    x * inclusion c a * x⁻¹ =
      inclusion c (ideleClassEquiv (projection c x).toRingEquiv a) :=
  NormalizedTwoCocycle.Extension.conjugate_inl c x a

theorem conjugation_mk (x : Extension c) (a : IdeleGroup (𝓞 E) E) :
    x * inclusion c (QuotientGroup.mk a) * x⁻¹ =
      inclusion c (QuotientGroup.mk (ideleEquiv (projection c x).toRingEquiv a)) := by
  rw [conjugation, ideleClassEquiv_mk]

end RelativeIdeleCocycle
end Langlands.ClassField.Global
