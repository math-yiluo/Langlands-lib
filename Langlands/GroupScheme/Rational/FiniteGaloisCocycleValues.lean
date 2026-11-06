import Langlands.GroupScheme.CocycleRefinement
import Langlands.GroupScheme.Descent.FiniteGaloisTensor
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints

/-! # Natural cocycles on a finite Galois cover are determined by Galois values -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]

/-- The point of the double cover `Spec L ×_K Spec L` given by the identity and the spectrum
map of a field automorphism. -/
def galoisPair (σ : L ≃ₐ[K] L) : ringTest K L ⟶ ringTest K L ⊗ ringTest K L :=
  CartesianMonoidalCategory.lift (𝟙 _) (ringTestMap K σ.toAlgHom)

@[reassoc (attr := simp)]
theorem galoisPair_fst (σ : L ≃ₐ[K] L) :
    galoisPair σ ≫ fst (ringTest K L) (ringTest K L) = 𝟙 _ :=
  CartesianMonoidalCategory.lift_fst _ _

@[reassoc (attr := simp)]
theorem galoisPair_snd (σ : L ≃ₐ[K] L) :
    galoisPair σ ≫ snd (ringTest K L) (ringTest K L) = ringTestMap K σ.toAlgHom :=
  CartesianMonoidalCategory.lift_snd _ _

variable [FiniteDimensional K L] [IsGalois K L]

/-- Two maps out of the double cover agree once they agree on every Galois pair. -/
theorem galoisPair_ext {W : Over (Spec (CommRingCat.of K))}
    {h₁ h₂ : ringTest K L ⊗ ringTest K L ⟶ W}
    (h : ∀ σ : L ≃ₐ[K] L, galoisPair σ ≫ h₁ = galoisPair σ ≫ h₂) : h₁ = h₂ := by
  apply Over.OverMorphism.ext
  refine (cancel_epi (Sigma.desc (Descent.finiteGaloisComponent K L))).1 ?_
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc_assoc]
  have hi : Descent.finiteGaloisComponent K L i =
      (galoisPair (Descent.galoisIndexEquiv K L i)).left := by
    apply pullback.hom_ext
    · rw [Descent.finiteGaloisComponent_fst]
      exact (congrArg (fun f => f.left) (galoisPair_fst (Descent.galoisIndexEquiv K L i))).symm
    · rw [Descent.finiteGaloisComponent_snd]
      exact (congrArg (fun f => f.left) (galoisPair_snd (Descent.galoisIndexEquiv K L i))).symm
  rw [hi]
  exact congrArg (fun f => f.left) (h (Descent.galoisIndexEquiv K L i))

variable {G : GroupScheme (Spec (CommRingCat.of K))}

/-- A natural cocycle on a finite Galois cover is determined by its values on the pairs
`(1, σ)` of Galois automorphisms. -/
theorem toFun_eq_of_galois_eq (ξ ζ : Cocycle G (ringTest K L))
    (h : ∀ σ : L ≃ₐ[K] L, ξ.toFun (𝟙 _) (ringTestMap K σ.toAlgHom) =
      ζ.toFun (𝟙 _) (ringTestMap K σ.toAlgHom))
    {Z : Over (Spec (CommRingCat.of K))} (a b : Z ⟶ ringTest K L) :
    ξ.toFun a b = ζ.toFun a b := by
  apply toFun_eq_of_universal_eq ξ ζ
  apply galoisPair_ext
  intro σ
  rw [← ξ.naturality, ← ζ.naturality, galoisPair_fst, galoisPair_snd]
  exact h σ

/-- A natural cocycle on a finite Galois cover is the coboundary of a cochain once the
coboundary equation holds on the pairs `(1, σ)` of Galois automorphisms. -/
theorem toFun_eq_coboundary_of_galois (ξ : Cocycle G (ringTest K L))
    (c : ringTest K L ⟶ G.X)
    (h : ∀ σ : L ≃ₐ[K] L, ξ.toFun (𝟙 _) (ringTestMap K σ.toAlgHom) =
      c * (ringTestMap K σ.toAlgHom ≫ c)⁻¹)
    {Z : Over (Spec (CommRingCat.of K))} (a b : Z ⟶ ringTest K L) :
    ξ.toFun a b = (a ≫ c) * (b ≫ c)⁻¹ := by
  refine toFun_eq_of_galois_eq ξ (coboundary c) (fun σ => ?_) a b
  rw [h σ]
  change c * (ringTestMap K σ.toAlgHom ≫ c)⁻¹ = (𝟙 _ ≫ c) * (ringTestMap K σ.toAlgHom ≫ c)⁻¹
  rw [Category.id_comp]

/-- The Galois coboundary criterion for triviality of a natural finite Galois cocycle. -/
theorem isTrivial_of_galois (ξ : Cocycle G (ringTest K L)) (c : ringTest K L ⟶ G.X)
    (h : ∀ σ : L ≃ₐ[K] L, ξ.toFun (𝟙 _) (ringTestMap K σ.toAlgHom) =
      c * (ringTestMap K σ.toAlgHom ≫ c)⁻¹) :
    ξ.IsTrivial :=
  ⟨c, fun a b => toFun_eq_coboundary_of_galois ξ c h a b⟩

end Langlands.GroupScheme.Cocycle
