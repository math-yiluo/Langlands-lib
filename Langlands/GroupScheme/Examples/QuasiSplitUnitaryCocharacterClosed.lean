import Langlands.GroupScheme.Examples.QuasiSplitUnitaryRankStatement
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryTensorCoordinates
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.CorepresentedAffineComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Algebra Opposite
open scoped TensorProduct CategoryTheory.MonObj LaurentPolynomial

namespace Langlands.GroupScheme.QuasiSplitUnitary

variable {F E : Type u} [Field F] [Field E] [Algebra F E] [IsQuadraticExtension F E]
  {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E)
  {I : Type u} (v : Module.Basis I F E)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem entryCoeff_cocharacter (T : Over (Spec (CommRingCat.of F)))
    (t : T ⟶ (Gm (Spec (CommRingCat.of F))).X) (i : Fin 2) (k : I) :
    entryCoeff v b c T (t ≫ (cocharacter b c).hom.hom) i i k =
      scalarMap T (v.repr (1 : E) k) *
        ((Gm.pointsEquiv _ T t ^ weights 1 i : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) := by
  unfold entryCoeff matrixCoordinates
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply]
  erw [pointsEquiv_weightCocharacter]
  simp only [diagonalUnitary_val, Matrix.diagonal_apply_eq]
  exact tensorCoeff_tmul v ((algΓ (CommRingCat.of F)).obj T).unop 1 _ k

/-- The cocharacter pulled back to the actual relative Laurent spectrum. -/
def cocharacterLaurentPoint : Gm.relativeLaurent (CommRingCat.of F) ⟶ (groupScheme b c).X :=
  Gm.laurentPoint F ≫ (cocharacter b c).hom.hom

/-- Its pullback on relative global sections, transported to the Laurent algebra. -/
def cocharacterLaurentMap :
    ((algΓ (CommRingCat.of F)).obj (groupScheme b c).X).unop →ₐ[F] F[T;T⁻¹] :=
  (Corepresented.affineSectionsAlgEquiv
    (CommAlgCat.of (CommRingCat.of F) F[T;T⁻¹])).toAlgHom.comp
      (((algΓ (CommRingCat.of F)).map (cocharacterLaurentPoint b c)).unop.hom)

theorem cocharacterLaurentMap_entryCoeff (i : Fin 2) (k : I) :
    cocharacterLaurentMap b c (entryCoeff v b c (groupScheme b c).X (𝟙 _) i i k) =
      LaurentPolynomial.C (v.repr (1 : E) k) * LaurentPolynomial.T (weights 1 i) := by
  change (Corepresented.affineSectionsAlgEquiv
      (CommAlgCat.of (CommRingCat.of F) F[T;T⁻¹]))
    ((cocharacterLaurentPoint b c).left.appTop
      (entryCoeff v b c (groupScheme b c).X (𝟙 _) i i k)) = _
  rw [← entryCoeff_comp]
  simp only [Category.comp_id, cocharacterLaurentPoint]
  rw [entryCoeff_cocharacter, map_mul]
  change (Corepresented.affineSectionsAlgEquiv
      (CommAlgCat.of (CommRingCat.of F) F[T;T⁻¹]))
    (algebraMap (CommRingCat.of F) _ (v.repr (1 : E) k)) * _ = _
  rw [AlgEquiv.commutes]
  congr 1
  change (Corepresented.affineSectionsIso
    (CommAlgCat.of (CommRingCat.of F) F[T;T⁻¹])).hom.hom.toRingHom _ = _
  rw [Corepresented.affineSectionsIso_hom_ringHom]
  erw [← Units.coe_map, ← map_zpow]
  change ((Gm.affinePointsEquiv _ (Gm.laurentPoint F ^ weights 1 i)).val : F[T;T⁻¹]) = _
  exact Gm.affinePointsEquiv_laurentPoint_zpow F (weights 1 i)

/-- Both Laurent generators are images of regular functions on the unitary group. -/
theorem cocharacterLaurentMap_T_mem (k : I) (hk : v.repr (1 : E) k ≠ 0) (i : Fin 2) :
    LaurentPolynomial.T (weights 1 i) ∈ (cocharacterLaurentMap b c).range := by
  let z : ((algΓ (CommRingCat.of F)).obj (groupScheme b c).X).unop :=
    entryCoeff v b c (groupScheme b c).X (𝟙 _) i i k
  refine ⟨algebraMap F _ ((v.repr (1 : E) k)⁻¹) * z, ?_⟩
  change cocharacterLaurentMap b c
    (algebraMap F _ ((v.repr (1 : E) k)⁻¹) * z) = _
  rw [map_mul, AlgHom.commutes]
  dsimp only [z]
  rw [cocharacterLaurentMap_entryCoeff]
  change LaurentPolynomial.C ((v.repr (1 : E) k)⁻¹) *
    (LaurentPolynomial.C (v.repr (1 : E) k) * LaurentPolynomial.T (weights 1 i)) = _
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, one_mul]

/-- The cocharacter is surjective on affine coordinate rings. -/
theorem cocharacterLaurentMap_surjective : Function.Surjective (cocharacterLaurentMap b c) := by
  classical
  let v := Module.Free.chooseBasis F E
  obtain ⟨k, hk⟩ : ∃ k, v.repr (1 : E) k ≠ 0 := by
    by_contra! h
    apply (one_ne_zero : (1 : E) ≠ 0)
    apply v.repr.injective
    ext k
    simpa using h k
  have hpos : LaurentPolynomial.T (1 : ℤ) ∈ (cocharacterLaurentMap b c).range := by
    simpa [weights] using cocharacterLaurentMap_T_mem b c v k hk 0
  have hneg : LaurentPolynomial.T (-1 : ℤ) ∈ (cocharacterLaurentMap b c).range := by
    simpa [weights] using cocharacterLaurentMap_T_mem b c v k hk 1
  intro p
  change p ∈ (cocharacterLaurentMap b c).range
  refine LaurentPolynomial.induction_on
    (M := fun q => q ∈ (cocharacterLaurentMap b c).range) p ?_ ?_ ?_ ?_
  · intro a
    exact (cocharacterLaurentMap b c).range.algebraMap_mem a
  · intro p q hp hq
    exact (cocharacterLaurentMap b c).range.add_mem hp hq
  · intro n a ha
    simpa only [mul_assoc, ← LaurentPolynomial.T_add, Nat.cast_add, Nat.cast_one] using
      (cocharacterLaurentMap b c).range.mul_mem ha hpos
  · intro n a ha
    simpa only [mul_assoc, ← LaurentPolynomial.T_add, sub_eq_add_neg] using
      (cocharacterLaurentMap b c).range.mul_mem ha hneg

/-- The explicit hyperbolic cocharacter is a closed subgroup of `U(1,1)`. -/
theorem isClosedSubgroup_cocharacter : IsClosedSubgroup (cocharacter b c) := by
  have hsurj : Function.Surjective (cocharacterLaurentPoint b c).left.appTop := by
    intro x
    obtain ⟨y, hy⟩ := cocharacterLaurentMap_surjective b c
      ((Corepresented.affineSectionsAlgEquiv
        (CommAlgCat.of (CommRingCat.of F) F[T;T⁻¹])) x)
    refine ⟨y, ?_⟩
    exact (Corepresented.affineSectionsAlgEquiv
      (CommAlgCat.of (CommRingCat.of F) F[T;T⁻¹])).injective hy
  have : IsAffine (Gm.relativeLaurent (CommRingCat.of F)).left := by
    change IsAffine (Spec (CommRingCat.of F[T;T⁻¹]))
    infer_instance
  have : IsClosedImmersion (cocharacterLaurentPoint b c).left :=
    IsClosedImmersion.of_surjective_of_isAffine _ hsurj
  let e := Gm.relativeLaurentIso (CommRingCat.of F)
  have heq : e.hom.left ≫ (cocharacterLaurentPoint b c).left =
      (cocharacter b c).hom.hom.left := by
    change (e.hom ≫ e.inv ≫ (cocharacter b c).hom.hom).left = _
    simp
  change IsClosedImmersion (cocharacter b c).hom.hom.left
  rw [← heq]
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  infer_instance

end Langlands.GroupScheme.QuasiSplitUnitary
