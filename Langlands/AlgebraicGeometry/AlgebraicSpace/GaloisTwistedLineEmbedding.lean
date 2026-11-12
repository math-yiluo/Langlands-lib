import Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisTwistedLineQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# The relation of the Galois-twisted line is an affine immersion

The map `R → U ×_K U` of the relation is the spectrum of the ring map
`K'[X] ⊗_K K'[X] → K'[X] × K'[X, 1/X]`, `a ⊗ b ↦ tStar a * sStar b`. This map becomes surjective
after inverting an element `c` whose image is `(1, X)`. So `R → U ×_K U` is a closed immersion
into the basic open `D(c)` followed by its inclusion: an immersion, and affine since both sides
are affine.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial TensorProduct
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace GaloisTwistedLine

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] (D : QuadraticConj K K')

variable (K) in
/-- The first relation map as a map of `K`-algebras. -/
def tStarAlg : K'[X] →ₐ[K] RelationRing K' :=
  { tStar with commutes' := fun _ => rfl }

/-- The second relation map as a map of `K`-algebras. -/
def sStarAlg : K'[X] →ₐ[K] RelationRing K' :=
  { sStar D with
    commutes' := fun k => by
      refine Prod.ext rfl ?_
      change algebraMap _ _ (conjPoly D (C (algebraMap K K' k))) = _
      rw [conjPoly_C, AlgEquiv.commutes]
      rfl }

/-- The ring map `a ⊗ b ↦ tStar a * sStar b`. -/
def tensorHom : K'[X] ⊗[K] K'[X] →+* RelationRing K' :=
  (Algebra.TensorProduct.lift (tStarAlg K) (sStarAlg D) (fun _ _ => Commute.all _ _)).toRingHom

theorem tensorHom_tmul (a b : K'[X]) : tensorHom D (a ⊗ₜ b) = tStar a * sStar D b :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem tensorHom_comp_includeLeft :
    (tensorHom D).comp Algebra.TensorProduct.includeLeftRingHom = tStar :=
  RingHom.ext fun a => by
    change tensorHom D (a ⊗ₜ 1) = _
    rw [tensorHom_tmul, map_one, mul_one]

theorem tensorHom_comp_includeRight :
    (tensorHom D).comp (Algebra.TensorProduct.includeRight (R := K) (A := K'[X])).toRingHom =
      sStar D :=
  RingHom.ext fun b => by
    change tensorHom D (1 ⊗ₜ b) = _
    rw [tensorHom_tmul, map_one, one_mul]

/-- The element of the tensor product mapping to `(0, 1)`. -/
def secondIdem : K'[X] ⊗[K] K'[X] :=
  (C D.θ ⊗ₜ 1 - 1 ⊗ₜ C D.θ) * (C (D.θ - D.σ D.θ)⁻¹ ⊗ₜ 1)

theorem tensorHom_secondIdem : tensorHom D (secondIdem D) = (0, 1) := by
  rw [secondIdem, map_mul, map_sub, tensorHom_tmul, tensorHom_tmul, tensorHom_tmul]
  simp only [map_one, mul_one, one_mul]
  refine Prod.ext ?_ ?_
  · simp [tStar, sStar]
  · simp only [tStar, sStar, RingHom.prod_apply, Prod.snd_mul, Prod.snd_sub, RingHom.coe_comp,
      Function.comp_apply, conjPoly_C]
    rw [← map_sub, ← map_mul, ← C_sub, ← C_mul,
      mul_inv_cancel₀ D.sub_ne_zero, C_1, map_one]

/-- The element of the tensor product mapping to `(1, X)`. -/
def unitElem : K'[X] ⊗[K] K'[X] := (1 - secondIdem D) + secondIdem D * (X ⊗ₜ 1)

theorem tensorHom_unitElem :
    tensorHom D (unitElem D) = (1, algebraMap K'[X] (PuncturedRing K') X) := by
  rw [unitElem, map_add, map_sub, map_one, map_mul, tensorHom_secondIdem, tensorHom_tmul,
    map_one, mul_one]
  ext <;> simp [tStar]

theorem isUnit_tensorHom_unitElem : IsUnit (tensorHom D (unitElem D)) := by
  rw [tensorHom_unitElem]
  exact (Prod.isUnit_iff).mpr ⟨isUnit_one, IsLocalization.Away.algebraMap_isUnit _⟩

/-- The relation ring as a quotient of the localization of the tensor product. -/
def locHom : Localization.Away (unitElem D) →+* RelationRing K' :=
  IsLocalization.Away.lift (unitElem D) (isUnit_tensorHom_unitElem D)

theorem locHom_comp : (locHom D).comp (algebraMap _ (Localization.Away (unitElem D))) =
    tensorHom D :=
  IsLocalization.Away.lift_comp _ _

theorem locHom_surjective : Function.Surjective (locHom D) := by
  have hmem : ∀ p, p ∈ Set.range (locHom D) := by
    have h1 : ∀ t, locHom D (algebraMap _ _ t) = tensorHom D t := fun t =>
      IsLocalization.Away.lift_eq _ _ _
    have hinv : locHom D (IsLocalization.Away.invSelf (unitElem D)) =
        (1, IsLocalization.Away.invSelf (X : K'[X])) := by
      have hu : locHom D (IsLocalization.Away.invSelf (unitElem D)) *
          tensorHom D (unitElem D) = 1 := by
        rw [← h1, ← map_mul, IsLocalization.Away.invSelf, IsLocalization.mk'_spec_mk, map_one,
          map_one]
      rw [tensorHom_unitElem] at hu
      have hu' : ((1 : K'[X]), IsLocalization.Away.invSelf (X : K'[X])) *
          (1, algebraMap K'[X] (PuncturedRing K') X) = 1 := by
        ext
        · simp
        · simp [IsLocalization.Away.invSelf, IsLocalization.mk'_spec_mk]
      calc locHom D (IsLocalization.Away.invSelf (unitElem D))
          = locHom D (IsLocalization.Away.invSelf (unitElem D)) *
              ((1, algebraMap K'[X] (PuncturedRing K') X) *
                (1, IsLocalization.Away.invSelf (X : K'[X]))) := by
            rw [mul_comm ((1 : K'[X]), _), hu', mul_one]
        _ = _ := by rw [← mul_assoc, hu, one_mul]
    rintro ⟨p, q⟩
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Submonoid.powers (X : K'[X])) q
    refine ⟨algebraMap _ _ ((1 - secondIdem D) * (p ⊗ₜ 1) + secondIdem D * (a ⊗ₜ 1)) *
      IsLocalization.Away.invSelf (unitElem D) ^ n, ?_⟩
    rw [map_mul, map_pow, hinv, h1, map_add, map_mul, map_mul, map_sub, map_one,
      tensorHom_secondIdem, tensorHom_tmul, tensorHom_tmul, map_one, mul_one, mul_one]
    have hpow : ((1 : K'[X]), IsLocalization.Away.invSelf (S := PuncturedRing K') (X : K'[X])) ^ n =
        (1, IsLocalization.Away.invSelf (S := PuncturedRing K') (X : K'[X]) ^ n) := by
      ext <;> simp
    refine Prod.ext ?_ ?_
    · simp [tStar, hpow]
    · rw [hpow]
      simp only [tStar, RingHom.prod_apply, RingHom.id_apply, Prod.snd_mul, Prod.snd_add,
        Prod.snd_sub, Prod.snd_one, sub_self, zero_mul, zero_add, one_mul]
      symm
      rw [IsLocalization.mk'_eq_iff_eq_mul]
      rw [mul_assoc, map_pow, ← mul_pow,
        mul_comm (IsLocalization.Away.invSelf (S := PuncturedRing K') (X : K'[X])),
        IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  exact fun p => hmem p

/-- **The relation is an immersion.** -/
theorem isImmersion_specTensorHom : IsImmersion (Spec.map (CommRingCat.ofHom (tensorHom D))) := by
  rw [← locHom_comp, CommRingCat.ofHom_comp, Spec.map_comp]
  have : _root_.AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom (locHom D))) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ (locHom_surjective D)
  infer_instance

theorem isAffineHom_specTensorHom : IsAffineHom (Spec.map (CommRingCat.ofHom (tensorHom D))) :=
  isAffineHom_of_isAffine _

/-- The relation map into the fibre product over `Spec K` is the spectrum of `tensorHom`, up to
the identifications of fibre products. -/
theorem prodLift_left_eq :
    (prod.lift (tOver D) (sOver D)).left =
      Spec.map (CommRingCat.ofHom (tensorHom D)) ≫ (pullbackSpecIso K K'[X] K'[X]).inv ≫
        (Over.prodLeftIsoPullback (lineOver K K') (lineOver K K')).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  apply pullback.hom_ext
  · rw [Category.assoc]
    erw [Over.prodLeftIsoPullback_hom_fst]
    rw [← Over.comp_left, prod.lift_fst, Category.assoc, pullbackSpecIso_inv_fst,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, tensorHom_comp_includeLeft]
    rfl
  · rw [Category.assoc]
    erw [Over.prodLeftIsoPullback_hom_snd]
    rw [← Over.comp_left, prod.lift_snd, Category.assoc, pullbackSpecIso_inv_snd,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact (congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (tensorHom_comp_includeRight D)).symm

/-- **The relation `R → U ×_K U` is an immersion.** -/
theorem isImmersion_prodLift : IsImmersion (prod.lift (tOver D) (sOver D)).left := by
  rw [prodLift_left_eq]
  have := isImmersion_specTensorHom D
  infer_instance

/-- **The relation `R → U ×_K U` is affine.** -/
theorem isAffineHom_prodLift : IsAffineHom (prod.lift (tOver D) (sOver D)).left := by
  rw [prodLift_left_eq]
  have := isAffineHom_specTensorHom D
  infer_instance

end GaloisTwistedLine

end Langlands.AlgebraicGeometry.AlgebraicSpace
