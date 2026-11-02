import Langlands.GroupScheme.Examples.QuasiSplitUnitaryAffineMatrices
import Langlands.GroupScheme.Torus.UniversalPoint
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {M N : Type u} [AddCommMonoid M] [AddCommMonoid N]

/-- Base change of a group algebra commutes with changing its exponent monoid. -/
theorem scalarTensorEquiv_mapDomain (f : M →+ N) (z : E ⊗[F] AddMonoidAlgebra F M) :
    AddMonoidAlgebra.scalarTensorEquiv F E
      (tensorCoefficientMap (AddMonoidAlgebra.mapDomainAlgHom F F f) z) =
    AddMonoidAlgebra.mapDomainAlgHom E E f
      (AddMonoidAlgebra.scalarTensorEquiv F E z) := by
  obtain ⟨p, rfl⟩ := (AddMonoidAlgebra.scalarTensorEquiv F E (M := M)).symm.surjective z
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | single m a =>
    simp [AddMonoidAlgebra.scalarTensorEquiv_symm_single,
      AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]

/-- Scalar conjugation becomes coefficientwise conjugation on the group algebra. -/
theorem scalarTensorEquiv_conjugation (c : E ≃ₐ[F] E)
    (z : E ⊗[F] AddMonoidAlgebra F M) :
    AddMonoidAlgebra.scalarTensorEquiv F E (scalarConjugation _ c z) =
      AddMonoidAlgebra.mapAlgHom M c.toAlgHom
        (AddMonoidAlgebra.scalarTensorEquiv F E z) := by
  obtain ⟨p, rfl⟩ := (AddMonoidAlgebra.scalarTensorEquiv F E (M := M)).symm.surjective z
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | single m a => simp

variable [IsQuadraticExtension F E]
variable {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E)

/-- Matrix coordinates over a group algebra, after scalar base change. -/
def groupAlgebraMatrixCoordinates (M : Type u) [AddCommMonoid M] :
    Lie.AffinePoints (groupScheme b c) (AddMonoidAlgebra F M) →*
      GL (Fin 2) (AddMonoidAlgebra E M) :=
  (Matrix.GeneralLinearGroup.map (AddMonoidAlgebra.scalarTensorEquiv F E (M := M)).toRingHom).comp
    (affineMatrixCoordinates b c (AddMonoidAlgebra F M))

/-- Group algebra matrix coordinates commute with exponent maps. -/
theorem groupAlgebraMatrixCoordinates_naturality (f : M →+ N)
    (x : Lie.AffinePoints (groupScheme b c) (AddMonoidAlgebra F M)) :
    groupAlgebraMatrixCoordinates b c N
      (Lie.affineMap _ (AddMonoidAlgebra.mapDomainAlgHom F F f) x) =
    Matrix.GeneralLinearGroup.map (AddMonoidAlgebra.mapDomainAlgHom E E f).toRingHom
      (groupAlgebraMatrixCoordinates b c M x) := by
  apply Units.ext
  change ((affineMatrixCoordinates b c _
    (Lie.affineMap _ (AddMonoidAlgebra.mapDomainAlgHom F F f) x)).val.map _) = _
  rw [affineMatrixCoordinates_naturality]
  apply Matrix.ext
  intro i j
  exact scalarTensorEquiv_mapDomain (F := F) (E := E) f
    (affineMatrixCoordinates b c _ x i j)

/-- The inverse matrix over the group algebra is its coefficientwise conjugate adjoint. -/
theorem groupAlgebraMatrixCoordinates_inv
    (x : Lie.AffinePoints (groupScheme b c) (AddMonoidAlgebra F M)) :
    (groupAlgebraMatrixCoordinates b c M x⁻¹).val =
      adjoint (AddMonoidAlgebra.mapAlgHom M c.toAlgHom)
        (groupAlgebraMatrixCoordinates b c M x).val := by
  change (affineMatrixCoordinates b c _ x⁻¹).val.map _ = _
  rw [affineMatrixCoordinates_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjoint, groupAlgebraMatrixCoordinates,
    scalarTensorEquiv_conjugation]

variable (I : Type u) [Fintype I] [DecidableEq I]
variable (i : splitTorus (Spec (CommRingCat.of F)) I ⟶ groupScheme b c)

/-- The matrix of the actual universal split-torus point under a unitary homomorphism. -/
def splitTorusUniversalMatrix : GL (Fin 2) (AddMonoidAlgebra E (I → ℤ)) :=
  groupAlgebraMatrixCoordinates b c (I → ℤ)
    (splitTorus.universalPoint I ≫ i.hom.hom)

/-- Addition of exponent maps multiplies the corresponding actual universal torus points. -/
theorem universalPoint_exponentMap_add (f g : (I → ℤ) →+ M) :
    Lie.affineMap _ (AddMonoidAlgebra.mapDomainAlgHom F F (f + g))
      (splitTorus.universalPoint (R := CommRingCat.of F) I) =
    Lie.affineMap _ (AddMonoidAlgebra.mapDomainAlgHom F F f)
        (splitTorus.universalPoint I) *
      Lie.affineMap _ (AddMonoidAlgebra.mapDomainAlgHom F F g)
        (splitTorus.universalPoint I) := by
  apply (splitTorus.algebraPointsEquiv I _).injective
  simp only [splitTorus.algebraPointsEquiv_naturality,
    map_mul]
  simp only [splitTorus.universalPoint, MulEquiv.apply_symm_apply]
  funext j
  apply Units.ext
  change AddMonoidAlgebra.mapDomainAlgHom F F (f + g)
      (AddMonoidAlgebra.single (Pi.single j 1) 1) =
    AddMonoidAlgebra.mapDomainAlgHom F F f
        (AddMonoidAlgebra.single (Pi.single j 1) 1) *
      AddMonoidAlgebra.mapDomainAlgHom F F g
        (AddMonoidAlgebra.single (Pi.single j 1) 1)
  simp [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.single_mul_single]

/-- Matrix multiplicativity over independent exponent maps. -/
theorem universalMatrix_map_add (f g : (I → ℤ) →+ M) :
    (splitTorusUniversalMatrix b c I i).val.map
        (AddMonoidAlgebra.mapDomainAlgHom E E (f + g)) =
      (splitTorusUniversalMatrix b c I i).val.map (AddMonoidAlgebra.mapDomainAlgHom E E f) *
        (splitTorusUniversalMatrix b c I i).val.map (AddMonoidAlgebra.mapDomainAlgHom E E g) := by
  have h := congrArg (fun x => groupAlgebraMatrixCoordinates b c M (x ≫ i.hom.hom))
    (universalPoint_exponentMap_add (F := F) I f g)
  rw [MonObj.mul_comp, map_mul] at h
  have hn (q : (I → ℤ) →+ M) := groupAlgebraMatrixCoordinates_naturality b c q
    (splitTorus.universalPoint I ≫ i.hom.hom)
  simp only [Lie.affineMap_apply, Category.assoc] at hn h
  rw [hn, hn, hn] at h
  exact congrArg Units.val h

/-- Negating exponent maps inverts the corresponding actual universal torus point. -/
theorem universalPoint_exponentMap_neg {N : Type u} [AddCommGroup N]
    (f : (I → ℤ) →+ N) :
    Lie.affineMap _ (AddMonoidAlgebra.mapDomainAlgHom F F (-f))
      (splitTorus.universalPoint (R := CommRingCat.of F) I) =
    (Lie.affineMap _ (AddMonoidAlgebra.mapDomainAlgHom F F f)
      (splitTorus.universalPoint I))⁻¹ := by
  apply (splitTorus.algebraPointsEquiv I _).injective
  simp only [splitTorus.algebraPointsEquiv_naturality,
    map_inv]
  simp only [splitTorus.universalPoint, MulEquiv.apply_symm_apply]
  funext j
  apply (eq_inv_iff_mul_eq_one).mpr
  apply Units.ext
  change AddMonoidAlgebra.mapDomainAlgHom F F (-f)
      (AddMonoidAlgebra.single (Pi.single j 1) 1) *
    AddMonoidAlgebra.mapDomainAlgHom F F f
      (AddMonoidAlgebra.single (Pi.single j 1) 1) = 1
  simp [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.one_def]

/-- Negating every exponent gives the conjugate adjoint of the universal matrix. -/
theorem universalMatrix_map_neg :
    (splitTorusUniversalMatrix b c I i).val.map
        (AddMonoidAlgebra.mapDomainAlgHom E E (-AddMonoidHom.id (I → ℤ))) =
      adjoint (AddMonoidAlgebra.mapAlgHom (I → ℤ) c.toAlgHom)
        (splitTorusUniversalMatrix b c I i).val := by
  have h := congrArg (fun x => groupAlgebraMatrixCoordinates b c (I → ℤ)
    (x ≫ i.hom.hom))
    (universalPoint_exponentMap_neg (F := F) I (AddMonoidHom.id (I → ℤ)))
  have hi (x : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of F)) I)
      (AddMonoidAlgebra F (I → ℤ))) : x⁻¹ ≫ i.hom.hom = (x ≫ i.hom.hom)⁻¹ :=
    map_inv ((pointsMap i).app (op _)).hom x
  rw [hi] at h
  have hn (q : (I → ℤ) →+ (I → ℤ)) :=
    groupAlgebraMatrixCoordinates_naturality b c q
      (splitTorus.universalPoint I ≫ i.hom.hom)
  rw [AddMonoidAlgebra.mapDomainAlgHom_id, Lie.affineMap_id] at h
  simp only [Lie.affineMap_apply, Category.assoc] at hn h
  rw [hn] at h
  have h' := congrArg Units.val h
  rw [groupAlgebraMatrixCoordinates_inv] at h'
  exact h'

end Langlands.GroupScheme.QuasiSplitUnitary
