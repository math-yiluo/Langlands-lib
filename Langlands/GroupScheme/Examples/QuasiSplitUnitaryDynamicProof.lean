import Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamicStatement
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryRootImages
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryOrbitNecessity

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [IsQuadraticExtension F E]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E) (m : ℤ)

/-- The matrix criterion for extending a unitary conjugation orbit across zero. -/
theorem mem_parabolic_weightCocharacter_iff {T : Over (Spec (CommRingCat.of F))}
    (g : T ⟶ (groupScheme b c).X) :
    g ∈ (Dynamic.parabolic (weightCocharacter b c m)).carrier T ↔
      matrixCoordinates b c T g ∈ GeneralLinear.blockParabolicSubgroup _ (weights m) :=
  ⟨matrixCoordinates_mem_blockParabolic_of_mem_parabolic (Module.Free.chooseBasis F E) b c m,
    mem_parabolic_of_blockParabolic b c m g⟩

/-- The matrix criterion for a constant unitary conjugation orbit. -/
theorem mem_centralizer_weightCocharacter_iff {T : Over (Spec (CommRingCat.of F))}
    (g : T ⟶ (groupScheme b c).X) :
    g ∈ (Dynamic.centralizer (weightCocharacter b c m)).carrier T ↔
      matrixCoordinates b c T g ∈ GeneralLinear.blockLeviSubgroup _ (weights m) :=
  ⟨matrixCoordinates_mem_blockLevi_of_mem_centralizer (Module.Free.chooseBasis F E) b c m,
    mem_centralizer_of_blockLevi b c m g⟩

/-- The matrix criterion for an identity limit of a unitary conjugation orbit. -/
theorem mem_unipotent_weightCocharacter_iff {T : Over (Spec (CommRingCat.of F))}
    (g : T ⟶ (groupScheme b c).X) :
    g ∈ (Dynamic.unipotent (weightCocharacter b c m)).carrier T ↔
      matrixCoordinates b c T g ∈ GeneralLinear.blockUnipotentSubgroup _ (weights m) :=
  ⟨matrixCoordinates_mem_blockUnipotent_of_mem_unipotent (Module.Free.chooseBasis F E) b c m,
    mem_unipotent_of_blockUnipotent b c m g⟩

/-- The positive hyperbolic cocharacter has upper triangular dynamic parabolic. -/
theorem parabolic_cocharacter :
    Dynamic.parabolic (cocharacter b c) = upperTriangular b c := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  exact mem_parabolic_weightCocharacter_iff b c 1 g

/-- The positive hyperbolic cocharacter has diagonal centralizer. -/
theorem centralizer_cocharacter :
    Dynamic.centralizer (cocharacter b c) = diagonal b c := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  exact mem_centralizer_weightCocharacter_iff b c 1 g

/-- The positive hyperbolic cocharacter has upper unipotent dynamic subgroup. -/
theorem unipotent_cocharacter :
    Dynamic.unipotent (cocharacter b c) = upperUnipotent b c := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  exact mem_unipotent_weightCocharacter_iff b c 1 g

/-- The negative hyperbolic cocharacter has lower triangular dynamic parabolic. -/
theorem parabolic_inverseCocharacter :
    Dynamic.parabolic (inverseCocharacter b c) = lowerTriangular b c := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  exact mem_parabolic_weightCocharacter_iff b c (-1) g

/-- The negative hyperbolic cocharacter has the same diagonal centralizer. -/
theorem centralizer_inverseCocharacter :
    Dynamic.centralizer (inverseCocharacter b c) = diagonal b c := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  change g ∈ (Dynamic.centralizer (weightCocharacter b c (-1))).carrier T ↔
    matrixCoordinates b c T g ∈ GeneralLinear.blockLeviSubgroup _ (weights 1)
  rw [← blockLeviSubgroup_weights_neg_one]
  exact mem_centralizer_weightCocharacter_iff b c (-1) g

/-- The negative hyperbolic cocharacter has lower unipotent dynamic subgroup. -/
theorem unipotent_inverseCocharacter :
    Dynamic.unipotent (inverseCocharacter b c) = lowerUnipotent b c := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  exact mem_unipotent_weightCocharacter_iff b c (-1) g

/-- All dynamic subgroup and trace-zero root-image descriptions of quasi-split U(1,1). -/
theorem dynamicStatement : DynamicStatement.{u} := by
  intro F E _ _ _ _ κ _ b c _
  exact ⟨parabolic_cocharacter b c, centralizer_cocharacter b c,
    unipotent_cocharacter b c, parabolic_inverseCocharacter b c,
    centralizer_inverseCocharacter b c, unipotent_inverseCocharacter b c,
    fun T => ⟨upperUnipotent_eq_range b c T, lowerUnipotent_eq_range b c T⟩⟩

end Langlands.GroupScheme.QuasiSplitUnitary
