/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Worker 105 adapts the universal-property functoriality of the published
Langlands.TauCeti.RingTheory.WeilRestriction.Basic (upstream commit
8428d6217f74afa72531df0bc85d7b57ab72810f) to finite-type input algebras.
The old finite-presentation interface is unchanged.
-/
import Langlands.RingTheory.WeilRestriction.FiniteType

/-! # Functoriality of finite-type affine Weil restriction -/

noncomputable section

open TensorProduct

namespace Langlands.Algebra.WeilRestrictionFiniteType

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  {C D E T : Type*} [CommRing C] [CommRing D] [CommRing E] [CommRing T]
  [Algebra B C] [Algebra B D] [Algebra B E] [Algebra A T]
  [Algebra.FiniteType B C] [Algebra.FiniteType B D] [Algebra.FiniteType B E]

/-- The canonical map classifying the composite with the universal point. -/
def map (φ : C →ₐ[B] D) :
    WeilRestrictionFiniteType A B C →ₐ[A] WeilRestrictionFiniteType A B D :=
  (homEquiv A B C _).symm ((universalPoint A B D).comp φ)

variable {A B}

theorem homEquiv_map (φ : C →ₐ[B] D) :
    homEquiv A B C _ (map A B φ) = (universalPoint A B D).comp φ :=
  Equiv.apply_symm_apply _ _

@[simp]
theorem lTensor_map_universalPoint (φ : C →ₐ[B] D) (c : C) :
    Algebra.TensorProduct.lTensor (S := B) B (map A B φ)
        (universalPoint A B C c) = universalPoint A B D (φ c) :=
  congrArg (fun f : C →ₐ[B] B ⊗[A] WeilRestrictionFiniteType A B D ↦ f c)
    (homEquiv_map φ)

/-- Contravariance of represented points in the coordinate algebra. -/
theorem homEquiv_comp_map (φ : C →ₐ[B] D)
    (g : WeilRestrictionFiniteType A B D →ₐ[A] T) :
    homEquiv A B C T (g.comp (map A B φ)) =
      (homEquiv A B D T g).comp φ := by
  rw [homEquiv_comp, homEquiv_map, homEquiv_apply, AlgHom.comp_assoc]

@[simp]
theorem map_id :
    map A B (AlgHom.id B C) = AlgHom.id A (WeilRestrictionFiniteType A B C) := by
  ext c
  simp

theorem map_comp (ψ : D →ₐ[B] E) (φ : C →ₐ[B] D) :
    map A B (ψ.comp φ) = (map A B ψ).comp (map A B φ) := by
  ext c
  simp [Algebra.TensorProduct.map_id_comp]

/-- The finite-type functor and the published finite-presentation functor
agree under their canonical representing-algebra comparisons. -/
theorem finitePresentationAlgEquiv_map
    [Algebra.FinitePresentation B C] [Algebra.FinitePresentation B D]
    (φ : C →ₐ[B] D) :
    (TauCeti.Algebra.WeilRestriction.map A B φ).comp
        (finitePresentationAlgEquiv A B C).toAlgHom =
      (finitePresentationAlgEquiv A B D).toAlgHom.comp (map A B φ) := by
  apply (homEquiv A B C _).injective
  rw [homEquiv_comp_finitePresentationAlgEquiv,
    TauCeti.Algebra.WeilRestriction.homEquiv_map, homEquiv_comp_map]
  simp only [homEquiv_apply, finitePresentationAlgEquiv_universalPoint]

end Langlands.Algebra.WeilRestrictionFiniteType
