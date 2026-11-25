import Langlands.RingTheory.WeilRestriction.FiniteType

/-! # Functoriality of the finite-type Weil restriction algebra

Let `B` be a finite projective `A`-algebra. For a `B`-algebra `C` of finite type,
`WeilRestrictionFiniteType A B C` represents the functor `T ↦ (C →ₐ[B] B ⊗[A] T)` on
`A`-algebras, through `homEquiv`. A homomorphism `φ : C →ₐ[B] D` acts on these functors by
precomposition, so it corresponds to a homomorphism of representing algebras
`map A B φ : WeilRestrictionFiniteType A B C →ₐ[A] WeilRestrictionFiniteType A B D`: the one
whose point is the universal point of `D` composed with `φ`. This file defines `map`, proves
that it respects identities and composition, and compares it with the map of
`Langlands.Algebra.WeilRestriction` when `C` and `D` are finitely presented.
-/

noncomputable section

open TensorProduct

namespace Langlands.Algebra.WeilRestrictionFiniteType

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  {C D E T : Type*} [CommRing C] [CommRing D] [CommRing E] [CommRing T]
  [Algebra B C] [Algebra B D] [Algebra B E] [Algebra A T]
  [Algebra.FiniteType B C] [Algebra.FiniteType B D] [Algebra.FiniteType B E]

/-- The homomorphism of Weil restriction algebras induced by `φ : C →ₐ[B] D`. Under the
representing bijection of `C` it corresponds to the universal point of `D` composed with
`φ`. -/
def map (φ : C →ₐ[B] D) :
    WeilRestrictionFiniteType A B C →ₐ[A] WeilRestrictionFiniteType A B D :=
  (homEquiv A B C _).symm ((universalPoint A B D).comp φ)

variable {A B}

theorem homEquiv_map (φ : C →ₐ[B] D) :
    homEquiv A B C _ (map A B φ) = (universalPoint A B D).comp φ :=
  (homEquiv A B C _).apply_symm_apply _

/-- `homEquiv_map`, evaluated at an element of `C`. -/
@[simp]
theorem lTensor_map_universalPoint (φ : C →ₐ[B] D) (c : C) :
    Algebra.TensorProduct.lTensor (S := B) B (map A B φ)
        (universalPoint A B C c) = universalPoint A B D (φ c) :=
  DFunLike.congr_fun (homEquiv_map (A := A) φ) c

/-- On points, composing with `map A B φ` is composing with `φ`. -/
theorem homEquiv_comp_map (φ : C →ₐ[B] D)
    (g : WeilRestrictionFiniteType A B D →ₐ[A] T) :
    homEquiv A B C T (g.comp (map A B φ)) =
      (homEquiv A B D T g).comp φ :=
  calc homEquiv A B C T (g.comp (map A B φ))
      = (Algebra.TensorProduct.lTensor B g).comp (homEquiv A B C _ (map A B φ)) :=
        homEquiv_comp _ _
    _ = (Algebra.TensorProduct.lTensor B g).comp ((universalPoint A B D).comp φ) := by
        rw [homEquiv_map]
    _ = (homEquiv A B D T g).comp φ := rfl

@[simp]
theorem map_id :
    map A B (AlgHom.id B C) = AlgHom.id A (WeilRestrictionFiniteType A B C) := by
  apply (homEquiv A B C _).injective
  rw [homEquiv_map, homEquiv_apply, AlgHom.comp_id]
  ext c
  simp

theorem map_comp (ψ : D →ₐ[B] E) (φ : C →ₐ[B] D) :
    map A B (ψ.comp φ) = (map A B ψ).comp (map A B φ) := by
  apply (homEquiv A B C _).injective
  rw [homEquiv_comp_map, homEquiv_map, homEquiv_map, AlgHom.comp_assoc]

/-- For finitely presented `C` and `D`, the comparison isomorphisms with
`Langlands.Algebra.WeilRestriction` carry `map A B φ` to the map of that construction. -/
theorem finitePresentationAlgEquiv_map
    [Algebra.FinitePresentation B C] [Algebra.FinitePresentation B D]
    (φ : C →ₐ[B] D) :
    (Langlands.Algebra.WeilRestriction.map A B φ).comp
        (finitePresentationAlgEquiv A B C).toAlgHom =
      (finitePresentationAlgEquiv A B D).toAlgHom.comp (map A B φ) := by
  -- Both sides have the point `(WeilRestriction.universalPoint A B D).comp φ`.
  apply (homEquiv A B C _).injective
  calc homEquiv A B C _ ((Langlands.Algebra.WeilRestriction.map A B φ).comp
          (finitePresentationAlgEquiv A B C).toAlgHom)
      = Langlands.Algebra.WeilRestriction.homEquiv A B C _
          (Langlands.Algebra.WeilRestriction.map A B φ) :=
        homEquiv_comp_finitePresentationAlgEquiv _
    _ = (Langlands.Algebra.WeilRestriction.universalPoint A B D).comp φ :=
        Langlands.Algebra.WeilRestriction.homEquiv_map φ
    _ = (homEquiv A B D _ (finitePresentationAlgEquiv A B D).toAlgHom).comp φ := by
        rw [homEquiv_apply, finitePresentationAlgEquiv_universalPoint]
    _ = homEquiv A B C _ ((finitePresentationAlgEquiv A B D).toAlgHom.comp (map A B φ)) :=
        (homEquiv_comp_map φ _).symm

end Langlands.Algebra.WeilRestrictionFiniteType
