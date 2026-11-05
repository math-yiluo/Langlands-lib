import Langlands.AlgebraicGeometry.ProjectiveSpace.BaseChange
import Langlands.Geometry.EtaleGaloisAction

/-! # Semilinear automorphisms of actual polynomial projective space -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

open Langlands.Geometry.EtaleGaloisAction

universe u

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (n : ℕ)

/-- The actual projective-space morphism fixing the original projective space
and acting on the base by the given algebra automorphism. -/
def galoisMap (σ : B ≃ₐ[R] B) : ProjectiveSpace B n ⟶ ProjectiveSpace B n :=
  (baseChangeMap_isPullback R B n).lift (baseChangeMap R B n)
    (projectiveSpaceToSpec B n ≫ specMap σ)
    (by rw [Category.assoc, specMap_comp_algebraMap]
        exact (baseChangeMap_isPullback R B n).w)

/-- The projective automorphism fixes the projection to the original projective space. -/
@[reassoc (attr := simp)]
theorem galoisMap_map (σ : B ≃ₐ[R] B) :
    galoisMap R B n σ ≫ baseChangeMap R B n = baseChangeMap R B n :=
  (baseChangeMap_isPullback R B n).lift_fst _ _ _

/-- The action on the structure morphism is the specified spectrum map. -/
@[reassoc (attr := simp)]
theorem galoisMap_toSpec (σ : B ≃ₐ[R] B) :
    galoisMap R B n σ ≫ projectiveSpaceToSpec B n =
      projectiveSpaceToSpec B n ≫ specMap σ :=
  (baseChangeMap_isPullback R B n).lift_snd _ _ _

@[simp]
theorem galoisMap_one :
    galoisMap R B n (1 : B ≃ₐ[R] B) = 𝟙 _ := by
  apply (baseChangeMap_isPullback R B n).hom_ext <;>
    simp [specMap_one]

/-- Raw projective comorphisms have the same order as raw spectrum comorphisms. -/
theorem galoisMap_mul (σ τ : B ≃ₐ[R] B) :
    galoisMap R B n (σ * τ) = galoisMap R B n σ ≫ galoisMap R B n τ := by
  apply (baseChangeMap_isPullback R B n).hom_ext <;>
    simp [← specMap_comp]

/-- The inverse algebra automorphism supplies the inverse projective morphism. -/
def galoisIso (σ : B ≃ₐ[R] B) : Aut (ProjectiveSpace B n) where
  hom := galoisMap R B n σ
  inv := galoisMap R B n σ⁻¹
  hom_inv_id := by rw [← galoisMap_mul, mul_inv_cancel, galoisMap_one]
  inv_hom_id := by rw [← galoisMap_mul, inv_mul_cancel, galoisMap_one]

/-- Inverse comorphisms give a left action on the specified projective-space scheme. -/
def galoisAction : (B ≃ₐ[R] B) →* Aut (ProjectiveSpace B n) where
  toFun σ := galoisIso R B n σ⁻¹
  map_one' := by
    apply Iso.ext
    exact galoisMap_one R B n
  map_mul' σ τ := by
    apply Iso.ext
    change galoisMap R B n ((σ * τ)⁻¹) =
      galoisMap R B n τ⁻¹ ≫ galoisMap R B n σ⁻¹
    rw [mul_inv_rev, galoisMap_mul]

/-- The bundled left action uses the inverse algebra automorphism. -/
@[simp]
theorem galoisAction_hom (σ : B ≃ₐ[R] B) :
    (galoisAction R B n σ).hom = galoisMap R B n σ⁻¹ := rfl

variable {R B n}
  {X X' : Scheme.{u}}
  {p : X ⟶ Spec (CommRingCat.of R)}
  {a : X' ⟶ X} {b : X' ⟶ Spec (CommRingCat.of B)}
  (sq : IsPullback a b p (Spec.map (CommRingCat.ofHom (algebraMap R B))))
  (i : X ⟶ ProjectiveSpace R n)
  (hi : i ≫ projectiveSpaceToSpec R n = p)

/-- Every semilinear source morphism fixing the original source intertwines
the actual base-change lift and the actual projective-space morphism. -/
theorem baseChangeLift_galoisMap
    (σ : B ≃ₐ[R] B) (g : X' ⟶ X')
    (ha : g ≫ a = a) (hb : g ≫ b = b ≫ specMap σ) :
    g ≫ baseChangeLift sq i hi =
      baseChangeLift sq i hi ≫ galoisMap R B n σ := by
  apply (baseChangeMap_isPullback R B n).hom_ext
  · simpa only [Category.assoc, baseChangeLift_map, galoisMap_map] using
      congrArg (fun k => k ≫ i) ha
  · simpa only [Category.assoc, baseChangeLift_toSpec,
      galoisMap_toSpec, baseChangeLift_toSpec_assoc] using hb

end Langlands.AlgebraicGeometry.ProjectiveSpace
