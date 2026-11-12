import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! # Faithfulness of smooth and normalized induction -/

noncomputable section

open CategoryTheory

namespace Langlands.Induction

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
  [CommRing R] [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Evaluation at a point as a linear map from smooth covariant functions. -/
def smoothEvaluation (P : Subgroup G) (σ : Representation R P V) (x : G) :
    SmoothFunctions P σ →ₗ[R] V where
  toFun f := eval P σ f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every coefficient vector is the value of an actual smooth induced function;
compact local sections supply preimages. -/
theorem smoothEvaluation_surjective [WeaklyLocallyCompactSpace G]
    (P : Subgroup G) (σ : Representation R P V) (hσ : IsSmooth σ) (x : G) :
    Function.Surjective (smoothEvaluation P σ x) := by
  intro v
  exact ⟨(compactLocalSection P σ hσ x v Set.univ isOpen_univ (Set.mem_univ _)).val,
    compactLocalSection_apply P σ hσ x v Set.univ isOpen_univ (Set.mem_univ _)⟩

/-- Induction is injective on intertwiners when the source coefficient action is
smooth. This is distinct from preservation of injective intertwiners. -/
theorem smoothInducedMap_injective_on_intertwiners
    [WeaklyLocallyCompactSpace G]
    (P : Subgroup G) {σ : Representation R P V} {τ : Representation R P W}
    (hσ : IsSmooth σ) :
    Function.Injective (fun f : σ.IntertwiningMap τ => smoothInducedMap P f) := by
  intro f g hfg
  ext v
  obtain ⟨s, hs⟩ := smoothEvaluation_surjective P σ hσ 1 v
  have hv := congrArg (fun a => eval P τ (a s) 1) hfg
  change f (smoothEvaluation P σ 1 s) = g (smoothEvaluation P σ 1 s) at hv
  rwa [hs] at hv

end Langlands.Induction

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] {P M U : Subgroup G}

/-- Normalized induction is faithful whenever its actual Levi projection is
continuous, so that every inflated, twisted coefficient representation is smooth. -/
theorem normalizedInductionFunctor_faithful (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hproj : Continuous h.projection) :
    (normalizedInductionFunctor.{uG, uV} h hU).Faithful where
  map_injective {A B} f g hfg := by
    have hsm : IsSmooth (inducingRepresentation h hU A) :=
      (isSmooth_twist_iff _ _
        (HaarModulus.isOpen_ker_closedHalfCharacter U hU P h.le_normalizer)).mpr
        (isSmooth_comp h.projection hproj A.isSmooth)
    let J := inflationFunctor.{uG, uV} h ⋙
      (inductionCharacter U P hU h.le_normalizer).twistFunctor
    have he : Induction.smoothInducedMap P (J.map f).hom =
        Induction.smoothInducedMap P (J.map g).hom :=
      congrArg SmoothRep.hom hfg
    have hf := Induction.smoothInducedMap_injective_on_intertwiners P hsm he
    ext v
    exact congrArg (fun a => a v) hf

end Langlands.Aubert.General
