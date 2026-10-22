import Langlands.Geometry.EtaleConstantCohomology

/-!
# Galois actions on étale cohomology of a base change

For a ring extension `K → L` and a scheme `X` over `Spec K`, the group of
`K`-algebra automorphisms of `L` acts on the base change `X ×_{Spec K} Spec L`
through the second factor. Hence it acts on the étale cohomology of the base
change with constant coefficients.
-/

noncomputable section

namespace Langlands.Geometry.EtaleGaloisAction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

variable (K : Type u) [CommRing K] (L : Type u) [CommRing L] [Algebra K L]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))

/-- The base change `X ×_{Spec K} Spec L`. -/
abbrev baseChange : Scheme.{u} := pullback f (Spec.algebraMap K L)

variable {K L}

/-- The automorphism of `Spec L` induced by a `K`-algebra automorphism. -/
def specMap (σ : L ≃ₐ[K] L) : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of L) :=
  Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)

theorem specMap_comp_algebraMap (σ : L ≃ₐ[K] L) :
    specMap σ ≫ Spec.algebraMap K L = Spec.algebraMap K L := by
  rw [specMap, Spec.algebraMap, ← Spec.map_comp]
  congr 1
  ext x
  simp

theorem specMap_comp (σ τ : L ≃ₐ[K] L) : specMap σ ≫ specMap τ = specMap (σ * τ) := by
  rw [specMap, specMap, specMap, ← Spec.map_comp]
  congr 1

theorem specMap_one : specMap (1 : L ≃ₐ[K] L) = 𝟙 _ := by
  rw [specMap, ← Spec.map_id]
  congr 1

/-- The endomorphism of the base change induced by a `K`-algebra automorphism
of `L`, acting on the second factor. -/
def baseChangeMap (σ : L ≃ₐ[K] L) : baseChange K L f ⟶ baseChange K L f :=
  pullback.map f (Spec.algebraMap K L) f (Spec.algebraMap K L) (𝟙 X) (specMap σ) (𝟙 _)
    (by simp) (by rw [Category.comp_id, specMap_comp_algebraMap])

theorem baseChangeMap_comp (σ τ : L ≃ₐ[K] L) :
    baseChangeMap f σ ≫ baseChangeMap f τ = baseChangeMap f (σ * τ) := by
  rw [baseChangeMap, baseChangeMap, pullback.map_comp]
  simp only [Category.comp_id, specMap_comp]
  rfl

theorem baseChangeMap_one : baseChangeMap f (1 : L ≃ₐ[K] L) = 𝟙 _ := by
  rw [baseChangeMap]
  simp only [specMap_one]
  exact pullback.map_id

/-- The automorphism of the base change induced by a `K`-algebra automorphism
of `L`. -/
def baseChangeAut (σ : L ≃ₐ[K] L) : Aut (baseChange K L f) where
  hom := baseChangeMap f σ
  inv := baseChangeMap f σ⁻¹
  hom_inv_id := by rw [baseChangeMap_comp, mul_inv_cancel, baseChangeMap_one]
  inv_hom_id := by rw [baseChangeMap_comp, inv_mul_cancel, baseChangeMap_one]

/-- The action of the `K`-algebra automorphisms of `L` on the base change.
The value at `σ` is the automorphism induced by `σ` on the second factor, in
the opposite of the automorphism group: the induced morphisms of spectra
compose contravariantly. -/
def galoisAut : (L ≃ₐ[K] L) →* (Aut (baseChange K L f))ᵐᵒᵖ where
  toFun σ := MulOpposite.op (baseChangeAut f σ)
  map_one' := by
    apply MulOpposite.unop_injective
    apply Iso.ext
    exact baseChangeMap_one f
  map_mul' σ τ := by
    apply MulOpposite.unop_injective
    apply Iso.ext
    exact (baseChangeMap_comp f σ τ).symm

variable (R : Type u) [CommRing R]

/-- The action of `L ≃ₐ[K] L` on degree `n` étale cohomology of the base change
`X ×_{Spec K} Spec L` with constant coefficients `M`. -/
def galoisCohomologyRep (M : ModuleCat.{u} R) (n : ℕ) : Rep.{u} R (L ≃ₐ[K] L) :=
  EtaleCohomologyAction.constantCohomologyRep R (galoisAut f) M n

end Langlands.Geometry.EtaleGaloisAction
