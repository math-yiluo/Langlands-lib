import Langlands.GroupScheme.Cartier.FiniteDualRelativePairing

/-! # Bijectivity of the Cartier comparison on affine tests -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry WithConv TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Cartier.FiniteDual

open Algebra.TensorProduct (includeLeft includeRight productMap)

variable (R : CommRingCat.{u}) (A : Type u) [CommRing A] [HopfAlgebra R A]
  [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Projective R A]

local notation "G" => specGroup R A
local notation "D" => specGroup R (Dual R A)
local notation "M" => Gm (Spec R)

local instance : GrpObj (specOver R A) := (G).grp

private def unitsOnSpectrum (B : Type u) [CommRing B] [Algebra R B] :
    (specOver R B ⟶ (M).X) ≃* Bˣ :=
  (Gm.pointsEquiv (Spec R) (specOver R B)).trans
    (Units.mapEquiv (sectionsSpec R B).toMulEquiv)

private theorem unitsOnSpectrum_naturality {B E : Type u} [CommRing B] [CommRing E]
    [Algebra R B] [Algebra R E] (h : B →ₐ[R] E) (z : specOver R B ⟶ (M).X) :
    unitsOnSpectrum R E (specMap h ≫ z) = Units.map h.toMonoidHom (unitsOnSpectrum R B z) := by
  apply Units.ext
  change sectionsSpec R E ((Gm.pointsEquiv (Spec R) (specOver R E) (specMap h ≫ z)).val) =
    h (sectionsSpec R B ((Gm.pointsEquiv (Spec R) (specOver R B) z).val))
  rw [Gm.pointsEquiv_naturality]
  exact sectionsSpec_naturality h _

variable {C : Type u} [CommRing C] [Algebra R C]

private def characterValue {B : Type u} [CommRing B] [Algebra R B]
    (χ : RelativeHom G M (specOver R C)) (c : C →ₐ[R] B) :
    WithConv (A →ₐ[R] B) →* Bˣ :=
  (unitsOnSpectrum R B).toMonoidHom.comp
    ((relativeHomLocalPoints G M χ (specMap c)).comp
      (Spec.mapMulEquiv (R := R) (S := A) (T := B)).toMonoidHom)

/-- A relative character supplies a coefficient by evaluation on the universal affine point. -/
private def tensorOfCharacter (χ : RelativeHom G M (specOver R C)) : A ⊗[R] C :=
  (characterValue R A χ (includeRight : C →ₐ[R] A ⊗[R] C) (toConv includeLeft)).val

omit [Module.Finite R A] [Module.Projective R A] in
private theorem characterValue_formula {B : Type u} [CommRing B] [Algebra R B]
    (χ : RelativeHom G M (specOver R C)) (c : C →ₐ[R] B) (x : WithConv (A →ₐ[R] B)) :
    (characterValue R A χ c x : B) = productMap x.ofConv c (tensorOfCharacter R A χ) := by
  let f := productMap x.ofConv c
  have hc : specMap c = specMap f ≫ specMap includeRight := by
    rw [← specMap_comp, Algebra.TensorProduct.productMap_right]
  have hx : specMap x.ofConv = specMap f ≫ specMap includeLeft := by
    rw [← specMap_comp, Algebra.TensorProduct.productMap_left]
  change (unitsOnSpectrum R B (relativeHomLocalPoints G M χ (specMap c) (specMap x.ofConv)) : B) =
    f (tensorOfCharacter R A χ)
  rw [hc, hx, relativeHomLocalPoints_naturality, unitsOnSpectrum_naturality]
  rfl

omit [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Projective R A] in
private theorem productMap_include (q : A →ₐ[R] A ⊗[R] A) :
    productMap ((includeLeft : (A ⊗[R] A) →ₐ[R] (A ⊗[R] A) ⊗[R] C).comp q)
        includeRight = Algebra.TensorProduct.map q (AlgHom.id R C) := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext'
  intro a c
  change ((q a ⊗ₜ[R] (1 : C)) * ((1 : A ⊗[R] A) ⊗ₜ[R] c)) = (q a ⊗ₜ[R] c)
  simp [Algebra.TensorProduct.tmul_mul_tmul]

omit [Module.Finite R A] [Module.Projective R A] in
private theorem tensorOfCharacter_groupLike (χ : RelativeHom G M (specOver R C)) :
    IsGroupLikeCoeff (tensorOfCharacter R A χ) := by
  let t := tensorOfCharacter R A χ
  constructor
  · have h := characterValue_formula R A χ (AlgHom.id R C) (1 : WithConv (A →ₐ[R] C))
    rw [map_one] at h
    exact h.symm
  · let q : (A ⊗[R] A) →ₐ[R] (A ⊗[R] A) ⊗[R] C := includeLeft
    let x₁ := toConv (q.comp (includeLeft : A →ₐ[R] A ⊗[R] A))
    let x₂ := toConv (q.comp (includeRight : A →ₐ[R] A ⊗[R] A))
    let c : C →ₐ[R] (A ⊗[R] A) ⊗[R] C := includeRight
    have hx : (x₁ * x₂).ofConv = q.comp (Bialgebra.comulAlgHom R A) := by
      dsimp only [x₁, x₂]
      rw [← AlgHom.comp_convMul_distrib, ← Langlands.Bialgebra.comulPoint_eq_include_mul]
    have h := congrArg Units.val (map_mul (characterValue R A χ c) x₁ x₂)
    change (characterValue R A χ c (x₁ * x₂) : (A ⊗[R] A) ⊗[R] C) =
      (characterValue R A χ c x₁ : (A ⊗[R] A) ⊗[R] C) *
        (characterValue R A χ c x₂ : (A ⊗[R] A) ⊗[R] C) at h
    rw [characterValue_formula, characterValue_formula, characterValue_formula, hx] at h
    change productMap (q.comp (Bialgebra.comulAlgHom R A)) c t =
      productMap (q.comp includeLeft) c t * productMap (q.comp includeRight) c t at h
    dsimp only [q, c] at h
    rw [productMap_include, productMap_include, productMap_include] at h
    exact h

omit [Module.Finite R A] [Module.Projective R A] in
private theorem tensorOfCharacter_injective :
    Function.Injective (tensorOfCharacter R A (C := C)) := by
  intro χ ψ h
  have hU : relativeHomLocalPoints G M χ (specMap (includeRight : C →ₐ[R] A ⊗[R] C))
        (specMap (includeLeft : A →ₐ[R] A ⊗[R] C)) =
      relativeHomLocalPoints G M ψ (specMap includeRight) (specMap includeLeft) :=
    (unitsOnSpectrum R _).injective (Units.ext h)
  apply relativeHom_ext
  intro V a x
  let c := (specHomEquiv V C).symm a
  let f := (specHomEquiv V A).symm x
  let p := specHomEquiv V (A ⊗[R] C) (productMap f c)
  have ha : p ≫ specMap includeRight = a := by
    apply (specHomEquiv V C).symm.injective
    rw [specHomEquiv_postcomp]
    dsimp only [p]
    rw [Equiv.symm_apply_apply, Algebra.TensorProduct.productMap_right]
  have hx : p ≫ specMap includeLeft = x := by
    apply (specHomEquiv V A).symm.injective
    rw [specHomEquiv_postcomp]
    dsimp only [p]
    rw [Equiv.symm_apply_apply, Algebra.TensorProduct.productMap_left]
  rw [← ha, ← hx, relativeHomLocalPoints_naturality,
    relativeHomLocalPoints_naturality, hU]

private theorem schemePairing_onSpectrum {B : Type u} [CommRing B] [Algebra R B]
    (y : Dual R A →ₐ[R] B) (x : A →ₐ[R] B) :
    unitsOnSpectrum R B (schemePairing R A (specOver R B) (specMap y) (specMap x)) =
      pointCharacter (toConv y) (toConv x) := by
  apply Units.ext
  change sectionsSpec R B ((Gm.pointsEquiv (Spec R) (specOver R B)
    (schemePairing R A (specOver R B) (specMap y) (specMap x))).val) = _
  rw [schemePairing_units, specPoints_specMap, specPoints_specMap, pointCharacter_postcomp]
  exact (sectionsSpec R B).apply_symm_apply _

private theorem tensorOfCharacter_ofPoint (y : Dual R A →ₐ[R] C) :
    tensorOfCharacter R A (characterOfPoint R A (specMap y)) =
      (coefficients R A C).symm y.toLinearMap := by
  change (unitsOnSpectrum R (A ⊗[R] C)
    (relativeHomLocalPoints G M (characterOfPoint R A (specMap y)) (specMap includeRight)
      (specMap includeLeft)) : A ⊗[R] C) = _
  rw [characterOfPoint_local, ← specMap_comp, schemePairing_onSpectrum,
    pointCharacter_baseChange_val]
  have h : productMap (includeLeft : A →ₐ[R] A ⊗[R] C) includeRight =
      AlgHom.id R (A ⊗[R] C) := by
    apply AlgHom.toLinearMap_injective
    exact TensorProduct.ext' fun a c => by
      change (a ⊗ₜ[R] (1 : C)) * ((1 : A) ⊗ₜ[R] c) = a ⊗ₜ[R] c
      simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [h, AlgHom.id_apply]

private theorem specMap_surjective {B : Type u} [CommRing B] [Algebra R B] :
    Function.Surjective (specMap : (B →ₐ[R] C) → (specOver R C ⟶ specOver R B)) := by
  intro y
  let f := (specHomEquiv (specOver R C) B).symm y
  refine ⟨(sectionsSpec R C).toAlgHom.comp f, (specHomEquiv (specOver R C) B).symm.injective ?_⟩
  rw [specHomEquiv_specMap]
  exact AlgHom.ext fun b => (sectionsSpec R C).symm_apply_apply (f b)

/-- On the spectrum of any coefficient algebra, all actual relative characters come from
exactly one dual point. -/
def affineCharacterEquiv (C : Type u) [CommRing C] [Algebra R C] :
    (specOver R C ⟶ (D).X) ≃ RelativeHom G M (specOver R C) :=
  Equiv.ofBijective (characterOfPoint R A) (by
    constructor
    · intro y z h
      obtain ⟨f, rfl⟩ := specMap_surjective R y
      obtain ⟨g, rfl⟩ := specMap_surjective R z
      have ht := congrArg (tensorOfCharacter R A) h
      rw [tensorOfCharacter_ofPoint, tensorOfCharacter_ofPoint] at ht
      exact congrArg specMap (AlgHom.toLinearMap_injective ((coefficients R A C).symm.injective ht))
    · intro χ
      let t := tensorOfCharacter R A χ
      let y := algHomOfCoeff t (tensorOfCharacter_groupLike R A χ)
      refine ⟨specMap y, tensorOfCharacter_injective R A ?_⟩
      rw [tensorOfCharacter_ofPoint, algHomOfCoeff_toLinearMap, LinearEquiv.symm_apply_apply])

theorem affineCharacterEquiv_apply (C : Type u) [CommRing C] [Algebra R C]
    (y : specOver R C ⟶ (D).X) :
    affineCharacterEquiv R A C y = characterOfPoint R A y := rfl

end Langlands.GroupScheme.Cartier.FiniteDual
