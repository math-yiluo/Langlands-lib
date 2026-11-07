import Langlands.ClassField.Global.LocalRelativeWeilMap

/-! # Local-to-relative Weil maps through the completed local class extension

Given a continuous homomorphism `κ` from the local Weil group `W_{F_v}` into the
extension `CompletionClassExtension v w a` of `Gal(E_w/F_v)` by `E_wˣ` for a local
fundamental class `a`, this module composes `κ` with the published
`RelativeWeilGroup.localToRelative`. It shows that the composite
satisfies `IsLocalRelativeWeilMap` when `κ` has the corresponding local properties. No
such `κ` is constructed here.
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u

namespace RelativeWeilGroup

attribute [local instance] completionGaloisTopology

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] (c : FundamentalClass.ClassFamily.{u})
  (v : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
  [w.asIdeal.LiesOver v.asIdeal]
  [IsGalois (padicField v).Carrier (w.adicCompletion E)]
  (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (h : FundamentalClass.LocalCompatibility I c)
  (a : CompletionH2 v w)
  (ha : IsFundamentalClass (padicField v).Carrier (w.adicCompletion E)
    ((I (residuePrime v)).relative (padicField v) (w.adicCompletion E)) a)

omit [IsGalois (padicField v).Carrier (w.adicCompletion E)] in
/-- A map into `W_{E/F}` continuous for the discrete topology `relativeGaloisTopology` on
`Gal(E/F)` is continuous for the Krull topology, which is the same topology. -/
theorem continuous_krull_of_relativeGalois {X : Type*} [TopologicalSpace X]
    (f : X → RelativeWeilGroup c F E)
    (hf : letI := relativeGaloisTopology F E
      Continuous f) :
    Continuous f := by
  rw [show krullTopology F E = relativeGaloisTopology F E from DiscreteTopology.eq_bot]
  exact hf

/-- The composite `W_{F_v} → CompletionClassExtension v w a → W_{E/F}` of a supplied map `κ` with
the published local-to-relative map, as a continuous homomorphism for the Krull topology
on `Gal(E/F)`. -/
def localWeilToRelative
    (κ : Weil.Local.localWeilGroup (padicField v) →ₜ* CompletionClassExtension v w a) :
    Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E :=
  let f : Weil.Local.localWeilGroup (padicField v) →* RelativeWeilGroup c F E :=
    letI := relativeGaloisTopology F E
    (localToRelative c v w I h a ha).toMonoidHom.comp κ.toMonoidHom
  have hf : letI := relativeGaloisTopology F E
      Continuous f := by
    let := relativeGaloisTopology F E
    exact (localToRelative c v w I h a ha).continuous_toFun.comp κ.continuous_toFun
  { toMonoidHom := f
    continuous_toFun := continuous_krull_of_relativeGalois c f hf }

/-- The composite is pointwise `localToRelative` applied to `κ g`. -/
theorem localWeilToRelative_apply
    (κ : Weil.Local.localWeilGroup (padicField v) →ₜ* CompletionClassExtension v w a)
    (g : Weil.Local.localWeilGroup (padicField v)) :
    localWeilToRelative c v w I h a ha κ g =
      letI := relativeGaloisTopology F E
      localToRelative c v w I h a ha (κ g) :=
  rfl

/-- If `κ` covers the Galois action of `W_{F_v}` on `E_w` and is the inverse of the
geometric reciprocity map on `W_{E_w}`, the composite is a local-to-relative Weil map. -/
theorem isLocalRelativeWeilMap_localWeilToRelative
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w))
    (he : LocalClassField.GeometricWeilReciprocityRelation (towerPadicField v w)
      (towerPadicField v w).canonicalTopologicalData e)
    (κ : Weil.Local.localWeilGroup (padicField v) →ₜ* CompletionClassExtension v w a)
    (hP : ∀ (g : Weil.Local.localWeilGroup (padicField v)) (y : w.adicCompletion E),
      completionClosureEmbedding v w (CompletionClassExtension.projection v w a (κ g) y) =
        AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField v) g)
          (completionClosureEmbedding v w y))
    (hR : ∀ y : Weil.Local.localWeilGroup (towerPadicField v w),
      κ (completionWeilMap v w y) =
        (CompletionClassExtension.inclusion v w a
          (LocalFactor.RankOne.reciprocityUnits (towerPadicField v w) e y))⁻¹) :
    IsLocalRelativeWeilMap v w e (localWeilToRelative c v w I h a ha κ) := by
  refine ⟨he, fun g x => ?_, fun y => ?_⟩
  · rw [localWeilToRelative_apply, projection_localToRelative, algebraMap_decompositionHom]
    exact hP g _
  · rw [localWeilToRelative_apply, hR, map_inv, localToRelative_inclusion]

end RelativeWeilGroup

end Langlands.ClassField.Global
