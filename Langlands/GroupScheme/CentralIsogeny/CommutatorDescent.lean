import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.ImageGenerationCommutator
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Descent of commutators through a homomorphism with central kernel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Commutators in an arbitrary group are unchanged by central factors. -/
theorem commutator_mul_central {M : Type*} [Group M] (a b z w : M)
    (hz : ∀ g, Commute z g) (hw : ∀ g, Commute w g) :
    (a * z) * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  calc (a * z) * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * (b * w)) * z⁻¹ * a⁻¹ * (b * w)⁻¹ := by group
    _ = a * ((b * w) * z) * z⁻¹ * a⁻¹ * (b * w)⁻¹ := by rw [(hz (b * w)).eq]
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [(hw a⁻¹).eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

namespace CommutatorDescent

variable {S : Scheme.{u}} {C G : GroupScheme S} (π : C ⟶ G)

/-- The commutator of a homomorphism image is the image of the commutator. -/
theorem tensorHom_commutatorMap :
    (π.hom.hom ⊗ₘ π.hom.hom) ≫ commutatorMap (𝟙 G) (𝟙 G) =
      commutatorMap (𝟙 C) (𝟙 C) ≫ π.hom.hom := by
  rw [← Category.id_comp ((π.hom.hom ⊗ₘ π.hom.hom) ≫ commutatorMap (𝟙 G) (𝟙 G)),
    ← Category.assoc, commutatorMap_points,
    ← Category.id_comp (commutatorMap (𝟙 C) (𝟙 C)), commutatorMap_points]
  simp only [Category.id_comp, tensorHom_fst, tensorHom_snd, Grp.id_hom_hom, Category.comp_id,
    MonObj.mul_comp, GrpObj.inv_comp]

variable (hπ : IsCentral (kernelι π))

include hπ

/-- Points with equal images differ by a central factor, so their commutators agree. -/
theorem commutator_eq_of_quotient_eq {T : Over S} (x y : T ⟶ C.X ⊗ C.X)
    (hxy : x ≫ (π.hom.hom ⊗ₘ π.hom.hom) = y ≫ (π.hom.hom ⊗ₘ π.hom.hom)) :
    x ≫ commutatorMap (𝟙 C) (𝟙 C) = y ≫ commutatorMap (𝟙 C) (𝟙 C) := by
  have h₁ : (x ≫ fst C.X C.X) ≫ π.hom.hom = (y ≫ fst C.X C.X) ≫ π.hom.hom := by
    simpa only [Category.assoc, tensorHom_fst] using congrArg (· ≫ fst G.X G.X) hxy
  have h₂ : (x ≫ snd C.X C.X) ≫ π.hom.hom = (y ≫ snd C.X C.X) ≫ π.hom.hom := by
    simpa only [Category.assoc, tensorHom_snd] using congrArg (· ≫ snd G.X G.X) hxy
  set a := x ≫ fst C.X C.X
  set b := x ≫ snd C.X C.X
  have central : ∀ {c d : T ⟶ C.X}, c ≫ π.hom.hom = d ≫ π.hom.hom →
      ∀ g, Commute (c⁻¹ * d) g := by
    intro c d hcd g
    have hk : (c⁻¹ * d) ≫ π.hom.hom = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hcd, inv_mul_cancel]
    exact commute_of_mem_center ((isCentral_kernelι_iff π).mp hπ T _ hk) g
  rw [commutatorMap_points, commutatorMap_points]
  simp only [Grp.id_hom_hom, Category.comp_id]
  rw [← mul_inv_cancel_left a (y ≫ fst C.X C.X), ← mul_inv_cancel_left b (y ≫ snd C.X C.X),
    commutator_mul_central a b _ _ (central h₁) (central h₂)]

/-- The same relation on arbitrary maps of underlying schemes. -/
theorem scheme_commutator_eq_of_quotient_eq {Z : Scheme.{u}} (x y : Z ⟶ (C.X ⊗ C.X).left)
    (hxy : x ≫ (π.hom.hom ⊗ₘ π.hom.hom).left = y ≫ (π.hom.hom ⊗ₘ π.hom.hom).left) :
    x ≫ (commutatorMap (𝟙 C) (𝟙 C)).left = y ≫ (commutatorMap (𝟙 C) (𝟙 C)).left := by
  have hs : y ≫ (C.X ⊗ C.X).hom = x ≫ (C.X ⊗ C.X).hom := by
    rw [← Over.w (π.hom.hom ⊗ₘ π.hom.hom), ← Category.assoc, ← hxy, Category.assoc]
  let x₀ : Over.mk (x ≫ (C.X ⊗ C.X).hom) ⟶ C.X ⊗ C.X := Over.homMk x rfl
  let y₀ : Over.mk (x ≫ (C.X ⊗ C.X).hom) ⟶ C.X ⊗ C.X := Over.homMk y hs
  exact congrArg (fun z => z.left)
    (commutator_eq_of_quotient_eq π hπ x₀ y₀ (Over.OverMorphism.ext hxy))

omit hπ

private abbrev fpqcProperty : MorphismProperty Scheme.{u} :=
  @QuasiCompact ⊓ (@Flat ⊓ @Surjective)

variable [QuasiCompact π.hom.hom.left] [Flat π.hom.hom.left] [Surjective π.hom.hom.left]

set_option backward.isDefEq.respectTransparency false in
/-- The square of an fpqc homomorphism is an effective epimorphism of schemes. -/
theorem effectiveEpi_tensorHom : EffectiveEpi (π.hom.hom ⊗ₘ π.hom.hom).left := by
  have hp : fpqcProperty (π.hom.hom ⊗ₘ π.hom.hom).left :=
    MorphismProperty.pullbackMap (P := fpqcProperty)
      ⟨inferInstance, inferInstance, inferInstance⟩
      ⟨inferInstance, inferInstance, inferInstance⟩
      (Over.w π.hom.hom).symm (Over.w π.hom.hom).symm
  let : QuasiCompact (π.hom.hom ⊗ₘ π.hom.hom).left := hp.1
  let : Flat (π.hom.hom ⊗ₘ π.hom.hom).left := hp.2.1
  let : Surjective (π.hom.hom ⊗ₘ π.hom.hom).left := hp.2.2
  infer_instance

/-- The square of an fpqc homomorphism is an epimorphism over the base. -/
theorem epi_tensorHom : Epi (π.hom.hom ⊗ₘ π.hom.hom) := by
  have := effectiveEpi_tensorHom π
  exact Over.epi_of_epi_left _

include hπ

/-- The descended underlying commutator morphism. -/
def schemeHom : (G.X ⊗ G.X).left ⟶ C.X.left :=
  haveI := effectiveEpi_tensorHom π
  EffectiveEpi.desc (π.hom.hom ⊗ₘ π.hom.hom).left (commutatorMap (𝟙 C) (𝟙 C)).left
    (fun x y hxy => scheme_commutator_eq_of_quotient_eq π hπ x y hxy)

@[reassoc]
theorem fac_schemeHom :
    (π.hom.hom ⊗ₘ π.hom.hom).left ≫ schemeHom π hπ = (commutatorMap (𝟙 C) (𝟙 C)).left :=
  haveI := effectiveEpi_tensorHom π
  EffectiveEpi.fac _ _ _

/-- Commutators of lifts, as a morphism out of the square of the target. -/
def hom : G.X ⊗ G.X ⟶ C.X :=
  Over.homMk (schemeHom π hπ) (by
    have := effectiveEpi_tensorHom π
    apply (cancel_epi (π.hom.hom ⊗ₘ π.hom.hom).left).mp
    rw [fac_schemeHom_assoc, Over.w, Over.w])

@[reassoc]
theorem fac : (π.hom.hom ⊗ₘ π.hom.hom) ≫ hom π hπ = commutatorMap (𝟙 C) (𝟙 C) :=
  Over.OverMorphism.ext (fac_schemeHom π hπ)

/-- On lifted points the descended morphism is the commutator of the lifts. -/
theorem lift_hom {T : Over S} (x y : T ⟶ C.X) :
    lift (x ≫ π.hom.hom) (y ≫ π.hom.hom) ≫ hom π hπ = x * y * x⁻¹ * y⁻¹ := by
  rw [← lift_map, Category.assoc, fac, commutatorMap_lift]
  simp only [Grp.id_hom_hom, Category.comp_id]

/-- Composing with the homomorphism recovers the commutator of the target. -/
theorem hom_comp : hom π hπ ≫ π.hom.hom = commutatorMap (𝟙 G) (𝟙 G) := by
  have := epi_tensorHom π
  apply (cancel_epi (π.hom.hom ⊗ₘ π.hom.hom)).mp
  rw [fac_assoc, tensorHom_commutatorMap]

/-- The identity pair maps to the identity. -/
theorem one_hom {T : Over S} : lift (1 : T ⟶ G.X) 1 ≫ hom π hπ = 1 := by
  have h := lift_hom π hπ (1 : T ⟶ C.X) 1
  simp only [MonObj.one_comp, mul_one, inv_one] at h
  exact h

end CommutatorDescent

end Langlands.GroupScheme
