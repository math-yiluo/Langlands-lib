import Langlands.GroupScheme.Examples.HermitianRootDynamicRoots
import Langlands.GroupScheme.Examples.HermitianRootNormalGeneration
import Langlands.GroupScheme.Rational.DynamicElementarySubgroup

/-! # Full weighted Hermitian images in the parabolic elementary subgroup -/

noncomputable section

universe u v z

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

section Coefficients

variable {A : Type u} {B : Type v} {Middle : Type z}
  [CommRing A] [CommRing B] [Fintype Middle]
  {c : RingInvolution A} {d : RingInvolution B}
  {H : DiagonalForm c Middle} {K : DiagonalForm d Middle}

/-- Compatible coefficient equivalences identify the original weighted parameters. -/
def Parameters.mapEquiv (e : A ≃+* B)
    (he : ∀ a, e (c.bar a) = d.bar (e a))
    (hH : ∀ i, e (H.weight i) = K.weight i) : Parameters H ≃* Parameters K where
  toFun := Parameters.map e.toRingHom he hH
  invFun := Parameters.map e.symm.toRingHom (involutionCompatible_symm e he)
    (weightCompatible_symm e hH)
  left_inv x := by
    apply Parameters.ext
    · funext i
      exact e.symm_apply_apply (x.vector i)
    · exact e.symm_apply_apply x.scalar
  right_inv x := by
    apply Parameters.ext
    · funext i
      exact e.apply_symm_apply (x.vector i)
    · exact e.apply_symm_apply x.scalar
  map_mul' := (Parameters.map e.toRingHom he hH).map_mul

variable [DecidableEq Middle]

/-- Compatible coefficient equivalence preserves the actual upper matrix. -/
theorem specialUnitaryRingEquiv_upper (e : A ≃+* B)
    (he : ∀ a, e (c.bar a) = d.bar (e a))
    (hH : ∀ i, e (H.weight i) = K.weight i) (x : Parameters H) :
    specialUnitaryRingEquiv e he hH (upperSpecialUnitaryHom H x) =
      upperSpecialUnitaryHom K (Parameters.mapEquiv e he hH x) := by
  apply Subtype.ext
  exact (Parameters.embedding_map e.toRingHom he hH x).symm

end Coefficients

namespace SchemeModel

open SU3Root.SchemeModel (baseAffineTest rationalCoefficientEquiv rationalCoefficientEquiv_bar)

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (fieldInvolution k L) Middle)
  (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)

/-- Evaluation of the actual tensor upper points gives the original rational upper points. -/
theorem rationalCoeffEquiv_rationalUpper
    (x : Parameters (tensorForm k L H (baseAffineTest k))) :
    GaloisPointComparison.rationalCoeffEquiv k (groupScheme k L H w hw)
        (rationalUpper k L H w hw (Parameters.mapEquiv
          (rationalCoefficientEquiv k L).toRingEquiv
          (rationalCoefficientEquiv_bar k L) (rationalCoefficientEquiv_weight k L H) x)) =
      upperPoints k L H w hw (baseAffineTest k) x := by
  apply (pointsEquiv k L H w hw (baseAffineTest k)).injective
  apply (specialUnitaryRingEquiv (rationalCoefficientEquiv k L).toRingEquiv
    (rationalCoefficientEquiv_bar k L) (rationalCoefficientEquiv_weight k L H)).injective
  change rationalMatrixEquiv k L H w hw (rationalUpper k L H w hw _) = _
  rw [pointsEquiv_upperPoints, specialUnitaryRingEquiv_upper]
  exact (rationalMatrixEquiv k L H w hw).apply_symm_apply _

/-- Every original rational upper point belongs to the actual upper subgroup at the identity test. -/
theorem rationalUpper_mem_upperFunctor (x : Parameters H) :
    rationalUpper k L H w hw x ∈ (upperFunctor k L H w hw).carrier (Over.mk (𝟙 _)) := by
  obtain ⟨y, rfl⟩ := (Parameters.mapEquiv
    (rationalCoefficientEquiv k L).toRingEquiv
    (rationalCoefficientEquiv_bar k L) (rationalCoefficientEquiv_weight k L H)).surjective x
  have hb : GaloisPointComparison.rationalCoeffEquiv k (groupScheme k L H w hw)
      (rationalUpper k L H w hw (Parameters.mapEquiv
        (rationalCoefficientEquiv k L).toRingEquiv
        (rationalCoefficientEquiv_bar k L) (rationalCoefficientEquiv_weight k L H) y)) ∈
      (upperFunctor k L H w hw).carrier (baseAffineTest k) := by
    rw [rationalCoeffEquiv_rationalUpper]
    exact ⟨y, rfl⟩
  have h := (upperFunctor k L H w hw).comp_mem
    (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).inv hb
  have heq : (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).inv ≫
      GaloisPointComparison.rationalCoeffEquiv k (groupScheme k L H w hw)
        (rationalUpper k L H w hw (Parameters.mapEquiv
          (rationalCoefficientEquiv k L).toRingEquiv
          (rationalCoefficientEquiv_bar k L) (rationalCoefficientEquiv_weight k L H) y)) =
      rationalUpper k L H w hw (Parameters.mapEquiv
        (rationalCoefficientEquiv k L).toRingEquiv
        (rationalCoefficientEquiv_bar k L) (rationalCoefficientEquiv_weight k L H) y) := by
    change (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).inv ≫
      ((Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).hom ≫ _) = _
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rwa [heq] at h

/-- Every original rational upper point contracts under the actual diagonal cocharacter. -/
theorem rationalUpper_range_le_dynamicUnipotent :
    (rationalUpper k L H w hw).range ≤
      (Dynamic.unipotent (cocharacter k L H w hw)).carrier (Over.mk (𝟙 _)) := by
  rintro _ ⟨x, rfl⟩
  exact upperFunctor_le_dynamicUnipotent k L H w hw _
    (rationalUpper_mem_upperFunctor k L H w hw x)

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Under middle anisotropy, a normal target subgroup containing the composed
upper dynamics contains the full rational image of the actual weighted scheme. -/
theorem rationalPoints_range_le_of_upper_dynamic (hH : H.IsAnisotropic)
    (f : groupScheme k L H w hw ⟶ G) (N : Subgroup (rationalPoints G)) [N.Normal]
    (hu : (Dynamic.unipotent (cocharacter k L H w hw ≫ f)).carrier (Over.mk (𝟙 _)) ≤ N) :
    (rationalPoints.map f).range ≤ N := by
  have htop : N.comap (rationalPoints.map f) = ⊤ := by
    apply eq_top_of_normal_upper_range k L H w hw hH
    rintro _ ⟨x, rfl⟩
    exact hu (Dynamic.unipotent_le_comap (cocharacter k L H w hw) f _
      (rationalUpper_range_le_dynamicUnipotent k L H w hw ⟨x, rfl⟩))
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ N.comap (rationalPoints.map f) := by
    rw [htop]
    trivial
  exact hx

/-- Every full rational image of the anisotropic-middle model lies in the actual
parabolic elementary subgroup of a connected reductive target. -/
theorem rationalPoints_range_le_parabolicElementarySubgroup (hH : H.IsAnisotropic)
    (hG : IsConnectedReductive G) (f : groupScheme k L H w hw ⟶ G) :
    (rationalPoints.map f).range ≤ parabolicElementarySubgroup G :=
  rationalPoints_range_le_of_upper_dynamic k L H w hw hH f (parabolicElementarySubgroup G)
    (dynamicUnipotent_le_parabolicElementarySubgroup hG (cocharacter k L H w hw ≫ f))

end SchemeModel
end Langlands.GroupScheme.HermitianRoot
