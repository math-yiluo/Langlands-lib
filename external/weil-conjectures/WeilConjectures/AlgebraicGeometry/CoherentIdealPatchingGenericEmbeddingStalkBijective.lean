/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentIdealPatchingGenericEmbeddingCore
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits ZeroObject AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

set_option linter.unusedVariables false in
/-- The factorization supplied by the core construction is bijective at the generic
stalk once its stalk map is known to be surjective. Source: Stacks Project, Tag 01YL,
final paragraph.
(blueprint: lem-weil-pbc-coherent-ideal-patching-generic-embedding-stalk-bijective)
Proof: combine the supplied surjectivity with monomorphy of the factorization; the
remaining geometric verification that the stalk map is surjective is isolated in the
core construction. -/
theorem coherent_ideal_patching_generic_embedding_stalk_bijective
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (ξ : X) (hclosure : closure ({ξ} : Set X) = Set.range i.base)
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hsupport : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base)
    (hkill : ∀ g : X.presheaf.stalk ξ,
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G,
        g ∈ IsLocalRing.maximalIdeal _ → g • m = 0)
    (I : Z.IdealSheafData) (r : ℕ)
    (M : X.Modules) (J : X.Modules) (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf)
    (τ : idealModuleProduct ι G ⟶ M) (hτ : Mono τ)
    (hτsurj : Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map τ).hom)
    (hι : Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map ι).hom) :
    Function.Bijective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map τ).hom := by
  have : Mono τ := hτ
  have : Mono τ.val := Functor.map_mono (SheafOfModules.forget _) τ
  refine ⟨?_, hτsurj⟩
  change Function.Injective (RingedSpace.stalkAddMap X.toRingedSpace ξ τ)
  dsimp only [RingedSpace.stalkAddMap]
  apply TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
  intro U
  exact PresheafOfModules.injective_of_mono τ.val (Opposite.op U)


end AlgebraicGeometry.Scheme.Modules
