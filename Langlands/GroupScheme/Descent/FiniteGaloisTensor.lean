import Langlands.GroupScheme.Descent.TensorComponents
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # The actual finite Galois tensor decomposition -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Descent

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- The canonical map to the product indexed by field automorphisms. -/
def galoisTensorHom : L ⊗[k] L →ₐ[L] ((L ≃ₐ[k] L) → L) :=
  AlgHom.pi fun σ => Algebra.TensorProduct.lift (AlgHom.id L L) σ.toAlgHom
    (fun _ _ => Commute.all _ _)

@[simp]
theorem galoisTensorHom_tmul (a b : L) (σ : L ≃ₐ[k] L) :
    galoisTensorHom k L (a ⊗ₜ[k] b) σ = a * σ b := rfl

/-- Distinct field automorphisms are linearly independent as functions. -/
theorem galoisFunctions_linearIndependent :
    LinearIndependent L (fun σ : L ≃ₐ[k] L => (σ : L → L)) := by
  exact (linearIndependent_monoidHom L L).comp
    (fun σ : L ≃ₐ[k] L => σ.toAlgHom.toRingHom.toMonoidHom)
    (fun σ τ h => DFunLike.ext _ _ fun b => congrArg (fun f : L →* L => f b) h)

/-- The evaluation tuples span the entire finite product. -/
theorem galoisTensorHom_surjective [FiniteDimensional k L] :
    Function.Surjective (galoisTensorHom k L) := by
  have hs : Submodule.span L (Set.range (fun b : L => fun σ : L ≃ₐ[k] L => σ b)) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr (galoisFunctions_linearIndependent k L)
  change Function.Surjective (galoisTensorHom k L).toLinearMap
  apply LinearMap.range_eq_top.mp
  apply top_le_iff.mp
  rw [← hs]
  apply Submodule.span_le.mpr
  rintro _ ⟨b, rfl⟩
  exact ⟨1 ⊗ₜ[k] b, by ext σ; simp⟩

/-- For a finite Galois extension, the canonical product map is bijective. -/
theorem galoisTensorHom_bijective [FiniteDimensional k L] [IsGalois k L] :
    Function.Bijective (galoisTensorHom k L) := by
  have hd : Module.finrank L (L ⊗[k] L) =
      Module.finrank L ((L ≃ₐ[k] L) → L) := by
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card,
      Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
  have hs := galoisTensorHom_surjective k L
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd
    (f := (galoisTensorHom k L).toLinearMap)).mpr hs, hs⟩

/-- The canonical finite Galois decomposition, as an actual algebra equivalence. -/
def galoisTensorEquiv [FiniteDimensional k L] [IsGalois k L] :
    (L ⊗[k] L) ≃ₐ[L] ((L ≃ₐ[k] L) → L) :=
  AlgEquiv.ofBijective (galoisTensorHom k L) (galoisTensorHom_bijective k L)

@[simp]
theorem galoisTensorEquiv_tmul [FiniteDimensional k L] [IsGalois k L]
    (a b : L) (σ : L ≃ₐ[k] L) :
    galoisTensorEquiv k L (a ⊗ₜ[k] b) σ = a * σ b := rfl

/-- Enumerate the Galois group by a genuinely small finite type. -/
def galoisIndexEquiv [FiniteDimensional k L] [IsGalois k L] :
    Fin (Module.finrank k L) ≃ (L ≃ₐ[k] L) :=
  (finCongr (Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank k L)).symm).trans
    (Fintype.equivFin _).symm

/-- The small-index version needed by the actual scheme component API. -/
def finiteGaloisTensorEquiv [FiniteDimensional k L] [IsGalois k L] :
    (L ⊗[k] L) ≃ₐ[L] (Fin (Module.finrank k L) → L) :=
  (galoisTensorEquiv k L).trans
    (AlgEquiv.piCongrLeft L (fun _ : L ≃ₐ[k] L => L) (galoisIndexEquiv k L)).symm

@[simp]
theorem finiteGaloisTensorEquiv_tmul [FiniteDimensional k L] [IsGalois k L]
    (a b : L) (i : Fin (Module.finrank k L)) :
    finiteGaloisTensorEquiv k L (a ⊗ₜ[k] b) i = a * galoisIndexEquiv k L i b := rfl

/-- The actual components of the double overlap of a finite Galois extension. -/
abbrev finiteGaloisComponent [FiniteDimensional k L] [IsGalois k L]
    (i : Fin (Module.finrank k L)) :
    Spec (CommRingCat.of L) ⟶ Overlap (fieldMap k L) :=
  tensorComponent (finiteGaloisTensorEquiv k L) i

/-- These actual components give an isomorphism from their finite coproduct. -/
instance finiteGaloisComponent_isIso_desc [FiniteDimensional k L] [IsGalois k L] :
    IsIso (Sigma.desc (finiteGaloisComponent k L)) :=
  tensorComponent_isIso_desc (finiteGaloisTensorEquiv k L)

@[reassoc (attr := simp)]
theorem finiteGaloisComponent_fst [FiniteDimensional k L] [IsGalois k L]
    (i : Fin (Module.finrank k L)) :
    finiteGaloisComponent k L i ≫ fst (fieldMap k L) = 𝟙 _ :=
  tensorComponent_fst _ _

@[reassoc (attr := simp)]
theorem finiteGaloisComponent_snd [FiniteDimensional k L] [IsGalois k L]
    (i : Fin (Module.finrank k L)) :
    finiteGaloisComponent k L i ≫ snd (fieldMap k L) =
      Spec.map (CommRingCat.ofHom (galoisIndexEquiv k L i).toRingHom) :=
  tensorComponent_snd _ (galoisIndexEquiv k L) (finiteGaloisTensorEquiv_tmul k L) i

end Langlands.GroupScheme.Descent
