import Langlands.GroupScheme.HomScheme.AdicBaseChange
import Langlands.AlgebraicGeometry.AffineQuotientPullback

/-! # Pullback of actual compatible adic Hom systems -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.AdicAffinePoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme.Adic

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The map on adic quotients induced by a ring homomorphism. -/
def quotientRingMap (φ : A →+* B) (I : Ideal A) (n : ℕ) :
    A ⧸ I ^ (n + 1) →+* B ⧸ (I.map φ) ^ (n + 1) :=
  Ideal.quotientMap ((I.map φ) ^ (n + 1)) φ
    (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)

/-- The map of affine quotient schemes induced by a ring homomorphism. -/
def quotientSpecMap (φ : A →+* B) (I : Ideal A) (n : ℕ) :
    quotientSpec (I.map φ) n ⟶ quotientSpec I n :=
  Spec.map (CommRingCat.ofHom (quotientRingMap φ I n))

@[reassoc] theorem quotientSpecMap_quotientMap (φ : A →+* B) (I : Ideal A) (n : ℕ) :
    quotientSpecMap φ I n ≫ quotientMap I n =
      quotientMap (I.map φ) n ≫ Spec.map (CommRingCat.ofHom φ) := by
  unfold quotientSpecMap quotientMap
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 1

@[reassoc] theorem quotientSpecMap_transition (φ : A →+* B) (I : Ideal A) (n : ℕ) :
    transition (I.map φ) n ≫ quotientSpecMap φ I (n + 1) =
      quotientSpecMap φ I n ≫ transition I n := by
  unfold quotientSpecMap transition
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 1
  ext x
  rfl

/-- Extended-ideal quotients form the actual Cartesian quotient square. -/
theorem isPullback_quotientSpecMap (φ : A →+* B) (I : Ideal A) (n : ℕ) :
    IsPullback (quotientSpecMap φ I n) (quotientMap (I.map φ) n)
      (quotientMap I n) (Spec.map (CommRingCat.ofHom φ)) := by
  have hgen (J : Ideal B) (hJ : (I ^ (n + 1)).map φ = J) :
      IsPullback
        (Spec.map (CommRingCat.ofHom (Ideal.quotientMap J φ
          (by rw [← hJ]; exact Ideal.le_comap_map))))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
        (quotientMap I n) (Spec.map (CommRingCat.ofHom φ)) := by
    subst J
    exact isPullback_SpecMap_of_isPushout _ _ _ _
      (Langlands.AlgebraicGeometry.isPushout_quotient_map φ (I ^ (n + 1)))
  exact hgen _ (Ideal.map_pow _ _ _)

instance quotientSpecMap_flat (φ : A →+* B) (I : Ideal A) (n : ℕ)
    [Flat (Spec.map (CommRingCat.ofHom φ))] : Flat (quotientSpecMap φ I n) :=
  MorphismProperty.of_isPullback (P := @Flat)
    (isPullback_quotientSpecMap φ I n).flip inferInstance

instance quotientSpecMap_surjective (φ : A →+* B) (I : Ideal A) (n : ℕ)
    [Surjective (Spec.map (CommRingCat.ofHom φ))] : Surjective (quotientSpecMap φ I n) :=
  MorphismProperty.of_isPullback (P := @Surjective)
    (isPullback_quotientSpecMap φ I n).flip inferInstance

/-- The quotient test over the extended ring viewed as a test over the original quotient. -/
def quotientOver (φ : A →+* B) (I : Ideal A) (n : ℕ) :
    (Over.map (Spec.map (CommRingCat.ofHom φ))).obj
        (Over.mk (quotientMap (I.map φ) n)) ⟶ Over.mk (quotientMap I n) :=
  Over.homMk (quotientSpecMap φ I n) (quotientSpecMap_quotientMap φ I n)

@[simp] theorem quotientOver_transition (φ : A →+* B) (I : Ideal A) (n : ℕ) :
    (Over.map (Spec.map (CommRingCat.ofHom φ))).map (transitionOver (I.map φ) n) ≫
        quotientOver φ I (n + 1) =
      quotientOver φ I n ≫ transitionOver I n := by
  apply Over.OverMorphism.ext
  exact quotientSpecMap_transition φ I n

namespace System

variable {I : Ideal A} {H G : GroupScheme (Spec (CommRingCat.of A))}

/-- Pull a compatible system to the image ideal of a ring map. -/
def pull (φ : A →+* B) (s : System I H G) :
    System (I.map φ) ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj H)
      ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj G) where
  hom n := unflatten (Spec.map (CommRingCat.ofHom φ))
    (Over.mk (quotientMap (I.map φ) n)) (evaluate (quotientOver φ I n) (s.hom n))
  compatible n := by
    apply (flattenEquiv (Spec.map (CommRingCat.ofHom φ))
      (Over.mk (quotientMap (I.map φ) n))).injective
    change flatten _ _ (evaluate _ _) = flatten _ _ _
    rw [flatten_evaluate, flatten_unflatten, flatten_unflatten, ← evaluate_comp,
      quotientOver_transition, evaluate_comp, s.compatible]

@[simp] theorem flatten_pull_hom (φ : A →+* B) (s : System I H G) (n : ℕ) :
    flatten (Spec.map (CommRingCat.ofHom φ)) (Over.mk (quotientMap (I.map φ) n))
        ((pull φ s).hom n) = evaluate (quotientOver φ I n) (s.hom n) :=
  flatten_unflatten _ _ _

/-- Restriction of an actual homomorphism commutes with pullback of its formal system. -/
@[simp] theorem pull_restrict (φ : A →+* B) (f : H ⟶ G) :
    pull φ (restrict I H G f) =
      restrict (I.map φ) _ _ ((baseChange (Spec.map (CommRingCat.ofHom φ))).map f) := by
  apply ext
  intro n
  apply (flattenEquiv (Spec.map (CommRingCat.ofHom φ))
    (Over.mk (quotientMap (I.map φ) n))).injective
  change flatten _ _ _ = flatten _ _ _
  rw [flatten_pull_hom]
  simp only [restrict_hom]
  erw [flatten_baseChange (Spec.map (CommRingCat.ofHom φ))
    (Over.mk (quotientMap (I.map φ) n)) ((baseChange (Spec.map (CommRingCat.ofHom φ))).map f)]
  exact (evaluate_baseChange (quotientOver φ I n) f).trans
    (evaluate_baseChange (Over.homMk (quotientMap (I.map φ) n) rfl :
      (Over.map (Spec.map (CommRingCat.ofHom φ))).obj
        (Over.mk (quotientMap (I.map φ) n)) ⟶
          Over.mk (Spec.map (CommRingCat.ofHom φ))) f).symm

/-- Pullback along a faithfully flat affine map detects compatible systems. -/
theorem pull_injective (φ : A →+* B) [Flat (Spec.map (CommRingCat.ofHom φ))]
    [Surjective (Spec.map (CommRingCat.ofHom φ))] :
    Function.Injective (pull (I := I) (H := H) (G := G) φ) := by
  intro s t h
  apply ext
  intro n
  have : Flat (quotientOver φ I n).left := quotientSpecMap_flat φ I n
  have : Surjective (quotientOver φ I n).left := quotientSpecMap_surjective φ I n
  have : QuasiCompact (quotientOver φ I n).left :=
    inferInstanceAs (QuasiCompact (quotientSpecMap φ I n))
  apply evaluate_injective_of_flat_surjective (quotientOver φ I n)
  have he := congrArg (fun k => flatten (Spec.map (CommRingCat.ofHom φ))
    (Over.mk (quotientMap (I.map φ) n)) (k.hom n)) h
  simpa only [flatten_pull_hom] using he

end System

end Langlands.GroupScheme.HomScheme.Adic
