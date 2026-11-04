import Langlands.GroupScheme.Dynamic.BaseChangeCoordinates
import Langlands.GroupScheme.Dynamic.DominantCombinationInclusions
import Langlands.CommutativeAlgebra.GradedDVRIntegralityTensor

/-! # Gradings and the comparison map of a homomorphism out of a base change

Let `G = Spec B` be a corepresented affine group over a field `k` with a cocharacter `λ`, let
`Ω` be a field extension of `k`, and let `π : G_Ω ⟶ H` be a homomorphism to an affine
`Ω`-group. Give `H` the cocharacter `λ_Ω ≫ π`. Then `comparisonMap π : Γ(H) → Ω ⊗[k] B` carries
the weight components of the coaction of `H` to the base-changed weight components of `B`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

open AffineLine

namespace Dynamic.AffineChart

variable {R : CommRingCat.{u}} {H : GroupScheme (Spec R)} [IsAffine H.X.left]
  (χ : (Gm (Spec R)).toGrp ⟶ H) {A : CommRingCat.{u}} {f : Spec A ⟶ Spec R}

/-- Conjugating a point over `Spec A` by `χ(u)` composes its classifying map with the coaction
and the evaluation at `u`. -/
theorem pointRing_conj (x : Over.mk f ⟶ H.X) (u : Aˣ) :
    pointRing ((unitPoint f u ≫ χ.hom.hom) * x * (unitPoint f u ≫ χ.hom.hom)⁻¹) =
      coaction χ ≫ laurentCoeffMap (pointRing x) ≫ laurentEval A u := by
  rw [← Dynamic.lift_comp_orbit, ← laurentAt_comp_laurentPoint, Category.assoc, pointRing_comp,
    pointRing_laurentPoint_comp_orbit, Category.assoc]
  congr 2
  exact Spec.preimage_map _

end Dynamic.AffineChart

namespace Corepresented

open CommutativeAlgebra.GradedDVRIntegrality

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  {Ω : Type u} [Field Ω] [Algebra k Ω]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra Ω A] [IsScalarTower k Ω A]

/-- The unit point `u` of `𝔾_{m,Ω}` over `Spec A`, regarded over `Spec k`, is the unit point `u`
of `𝔾_{m,k}`. -/
theorem testOverHom_comp_unitPoint (u : Aˣ) :
    testOverHom (k := k) Ω A ≫ baseChangePointsEquiv (scalarMap k Ω)
        (Gm (Spec (CommRingCat.of k))).toGrp (testOver Ω A)
        (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap Ω A))) u ≫
          (Gm.baseChangeIso (scalarMap k Ω)).inv.hom.hom) =
      unitPoint (Spec.map (CommRingCat.ofHom (algebraMap k A))) u := by
  apply (Gm.pointsEquiv _ _).injective
  rw [Gm.pointsEquiv_naturality, ← Gm.baseChangeUnitsEquiv_apply,
    Gm.baseChangeUnitsEquiv_baseChangeIso_inv, unitPoint, unitPoint, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]
  ext
  change (𝟙 (Spec (CommRingCat.of A)) : _ ⟶ _).appTop _ = _
  rw [Scheme.Hom.id_appTop]
  rfl

variable (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme F e)

/-- Conjugation by a base-changed cocharacter corresponds to conjugation by the cocharacter. -/
theorem basePoint_conj (z : testOver Ω A ⟶ (baseChangeGroup F e Ω).X) (u : Aˣ) :
    basePoint ((unitPoint (Spec.map (CommRingCat.ofHom (algebraMap Ω A))) u ≫
          (Dynamic.baseChangeCocharacter (scalarMap k Ω) ν).hom.hom) * z *
        (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap Ω A))) u ≫
          (Dynamic.baseChangeCocharacter (scalarMap k Ω) ν).hom.hom)⁻¹) =
      (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap k A))) u ≫ ν.hom.hom) * basePoint z *
        (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap k A))) u ≫ ν.hom.hom)⁻¹ := by
  rw [basePoint, map_mul, map_mul, map_inv, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
    Dynamic.baseChangePointsEquiv_baseChangeCocharacter, ← Category.assoc,
    testOverHom_comp_unitPoint]
  rfl

section Grading

variable {H : GroupScheme (Spec (CommRingCat.of Ω))} [IsAffine H.X.left]
  (π : baseChangeGroup F e Ω ⟶ H)

variable (B Ω) in
/-- The inclusion `B → (Ω ⊗[k] B)[T, T⁻¹]` as constants. -/
def laurentEmbedding : B →ₐ[k] LaurentPolynomial (Ω ⊗[k] B) :=
  (IsScalarTower.toAlgHom k (Ω ⊗[k] B) (LaurentPolynomial (Ω ⊗[k] B))).comp
    Algebra.TensorProduct.includeRight

theorem classifying_bcPoint_laurentEmbedding :
    CommRingCat.ofHom (classifying (bcPoint F e Ω _ (laurentEmbedding B Ω))).toRingHom =
      Gm.laurentC (CommRingCat.of (Ω ⊗[k] B)) := by
  have h : ∀ m : Ω ⊗[k] B,
      classifying (bcPoint F e Ω _ (laurentEmbedding B Ω)) m = LaurentPolynomial.C m := by
    intro m
    induction m with
    | tmul ω b =>
      rw [classifying, Algebra.TensorProduct.lift_tmul, pointAlgHom_basePoint_bcPoint]
      change LaurentPolynomial.C (ω ⊗ₜ[k] (1 : B)) * LaurentPolynomial.C ((1 : Ω) ⊗ₜ[k] b) = _
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact CommRingCat.hom_ext (RingHom.ext h)

theorem coeff_classifying_conj (m : Ω ⊗[k] B) (n : ℤ) :
    (classifying ((unitPoint (Spec.map (CommRingCat.ofHom
          (algebraMap Ω (LaurentPolynomial (Ω ⊗[k] B))))) (Gm.relativeCoordUnit (Ω ⊗[k] B)) ≫
          (Dynamic.baseChangeCocharacter (scalarMap k Ω) ν).hom.hom) *
        bcPoint F e Ω _ (laurentEmbedding B Ω) *
        (unitPoint (Spec.map (CommRingCat.ofHom
          (algebraMap Ω (LaurentPolynomial (Ω ⊗[k] B))))) (Gm.relativeCoordUnit (Ω ⊗[k] B)) ≫
          (Dynamic.baseChangeCocharacter (scalarMap k Ω) ν).hom.hom)⁻¹) m).coeff n =
      (weightPart (isGrading_coaction ν) n).lTensor Ω m := by
  have hpt : ∀ b : B, pointAlgHom (basePoint ((unitPoint (Spec.map (CommRingCat.ofHom
          (algebraMap Ω (LaurentPolynomial (Ω ⊗[k] B))))) (Gm.relativeCoordUnit (Ω ⊗[k] B)) ≫
          (Dynamic.baseChangeCocharacter (scalarMap k Ω) ν).hom.hom) *
        bcPoint F e Ω _ (laurentEmbedding B Ω) *
        (unitPoint (Spec.map (CommRingCat.ofHom
          (algebraMap Ω (LaurentPolynomial (Ω ⊗[k] B))))) (Gm.relativeCoordUnit (Ω ⊗[k] B)) ≫
          (Dynamic.baseChangeCocharacter (scalarMap k Ω) ν).hom.hom)⁻¹)) b =
        laurentCoeffMap (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : B →ₐ[k] Ω ⊗[k] B).toRingHom) (coaction ν b) := by
    intro b
    rw [pointAlgHom_apply, basePoint_conj, basePoint_bcPoint, pointRing_conj]
    have h1 : pointRing (ofAlgHom F e (laurentEmbedding B Ω)) =
        CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[k] Ω ⊗[k] B).toRingHom ≫
          Gm.laurentC (CommRingCat.of (Ω ⊗[k] B)) := by
      change Spec.preimage (Spec.map _) = _
      rw [Spec.preimage_map]
      rfl
    rw [h1, laurentCoeffMap_comp_laurentC_comp_laurentEval]
    rfl
  induction m with
  | tmul ω b =>
    rw [classifying, Algebra.TensorProduct.lift_tmul, hpt, LinearMap.lTensor_tmul,
      weightPart_apply]
    change (LaurentPolynomial.C (ω ⊗ₜ[k] (1 : B)) * _).coeff n = _
    rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single_zero_mul,
      coeff_laurentCoeffMap]
    change ω ⊗ₜ[k] (1 : B) * (1 ⊗ₜ[k] (coaction ν b).coeff n) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy, map_add]

/-- **Equivariance of the comparison map.** The comparison map carries the weight components of
the coaction of `λ_Ω ≫ π` on `Γ(H)` to the base-changed weight components on `Ω ⊗[k] B`. -/
theorem lTensor_weightPart_comparisonMap (f'' : Γ(H.X.left, ⊤)) (n : ℤ) :
    (weightPart (isGrading_coaction ν) n).lTensor Ω (comparisonMap π f'') =
      comparisonMap π ((Dynamic.AffineChart.coaction
        (Dynamic.baseChangeCocharacter (scalarMap k Ω) ν ≫ π) f'').coeff n) := by
  set f₁ := Spec.map (CommRingCat.ofHom (algebraMap Ω (LaurentPolynomial (Ω ⊗[k] B))))
  set t := Gm.relativeCoordUnit (Ω ⊗[k] B)
  set x₁ := bcPoint F e Ω _ (laurentEmbedding B Ω)
  have key : Dynamic.AffineChart.pointRing
      ((unitPoint f₁ t ≫ (Dynamic.baseChangeCocharacter (scalarMap k Ω) ν ≫ π).hom.hom) *
        (x₁ ≫ π.hom.hom) *
        (unitPoint f₁ t ≫ (Dynamic.baseChangeCocharacter (scalarMap k Ω) ν ≫ π).hom.hom)⁻¹) =
      Dynamic.AffineChart.pointRing
        (((unitPoint f₁ t ≫ (Dynamic.baseChangeCocharacter (scalarMap k Ω) ν).hom.hom) * x₁ *
          (unitPoint f₁ t ≫ (Dynamic.baseChangeCocharacter (scalarMap k Ω) ν).hom.hom)⁻¹) ≫
          π.hom.hom) := by
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]
    rfl
  rw [Dynamic.AffineChart.pointRing_conj, pointRing_comp_eq, pointRing_comp_eq,
    classifying_bcPoint_laurentEmbedding, laurentCoeffMap_comp_laurentC_comp_laurentEval] at key
  have h := congrArg (fun φ => (φ.hom f'').coeff n) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  rw [AddMonoidAlgebra.coeff_mapRingHom] at h
  rw [h]
  exact (coeff_classifying_conj ν _ n).symm

end Grading

end Corepresented

end Langlands.GroupScheme
