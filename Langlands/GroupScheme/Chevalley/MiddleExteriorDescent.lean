import Langlands.GroupScheme.Chevalley.MiddleExteriorCocycle
import Langlands.LinearAlgebra.UnitaryTwistedChart
import Langlands.Algebra.UnitaryDiscriminant.Class
import Langlands.Algebra.BrauerComparison.ProjectiveDescent

/-! # The descended middle exterior matrix algebra -/

noncomputable section

open Matrix
open scoped TensorProduct

universe u

namespace Langlands.LinearAlgebra.UnitaryTwistedChart.Cocycle

open CentralSimple CentralSimple.SemilinearGaloisAction GroupScheme.Chevalley
open UnitaryDiscriminant

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
  {F : IntermediateField K M} {m : ℕ} (c : Cocycle F (Fin (2 * m)))

abbrev MiddleExteriorIndices (m : ℕ) := Set.powersetCard (Fin (2 * m)) m

theorem middleExteriorIndices_nonempty (m : ℕ) : Nonempty (MiddleExteriorIndices m) := by
  obtain ⟨s, hs⟩ := Finset.powersetCard_nonempty.mpr
    (show m ≤ (Finset.univ : Finset (Fin (2 * m))).card by
      rw [Finset.card_univ, Fintype.card_fin]
      omega)
  exact ⟨⟨s, (Finset.mem_powersetCard.mp hs).2⟩⟩

attribute [local instance] middleExteriorIndices_nonempty coefficientGLAction

private theorem centerFixing_eq : centerFixing K F M = F.fixingSubgroup := by
  ext g
  rw [mem_centerFixing, IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h y hy => h ⟨y, hy⟩, fun h y => h y y.2⟩

private theorem exists_exteriorFactor (s t : Gal(M/K)) :
    ∃ a : Mˣ, c.x s * twistGL F.fixingSubgroup s (c.x t) =
      GeneralLinearGroup.scalar (Fin (2 * m)) a * c.x (s * t) :=
  exists_twistGL_mul_eq (fun _ _ => Subgroup.mul_mem_iff_of_index_two c.index_eq) c.x
    (UnitaryTwistedDescent.twistedAct_mul c.index_eq c.inner c.outer) s t

private def exteriorFactor (s t : Gal(M/K)) : Mˣ :=
  (c.exists_exteriorFactor s t).choose

private theorem exteriorFactor_spec (s t : Gal(M/K)) :
    c.x s * twistGL F.fixingSubgroup s (c.x t) =
      GeneralLinearGroup.scalar (Fin (2 * m)) (c.exteriorFactor s t) * c.x (s * t) :=
  (c.exists_exteriorFactor s t).choose_spec

private theorem middleExteriorFactor_spec (s t : Gal(M/K)) :
    (middleExteriorLift m F.fixingSubgroup c.x s : GL (MiddleExteriorIndices m) M) *
        (s • middleExteriorLift m F.fixingSubgroup c.x t) =
      GeneralLinearGroup.scalar (MiddleExteriorIndices m)
        (detCocycle F.fixingSubgroup c.x c.exteriorFactor m s t) *
        middleExteriorLift m F.fixingSubgroup c.x (s * t) :=
  middleExteriorLift_mul m F.fixingSubgroup c.x
    (Subgroup.mul_mem_iff_of_index_two c.index_eq) c.exteriorFactor (c.exteriorFactor_spec s t)

/-- The original matrix lifts induce an ordinary projective action on the middle
exterior powers. It acts semilinearly on their endomorphism algebra. -/
def middleExteriorAction : SemilinearGaloisAction K M
    (Matrix (MiddleExteriorIndices m) (MiddleExteriorIndices m) M) :=
  ofProjectiveLifts (I := MiddleExteriorIndices m) (middleExteriorLift m F.fixingSubgroup c.x)
    c.middleExteriorFactor_spec

theorem middleExteriorAction_act (s : Gal(M/K))
    (X : Matrix (MiddleExteriorIndices m) (MiddleExteriorIndices m) M) :
    c.middleExteriorAction.act s X =
      (middleExteriorLift m F.fixingSubgroup c.x s : Matrix _ _ M) * X.map s *
        (↑((middleExteriorLift m F.fixingSubgroup c.x s)⁻¹) :
          Matrix (MiddleExteriorIndices m) (MiddleExteriorIndices m) M) := rfl

variable [FiniteDimensional K M] [IsGalois K M]

/-- The matrix algebra of the middle exterior power descended to `K`. -/
abbrev middleExteriorCSA : CSA.{u, u} K := matrixFixedCSA c.middleExteriorAction

/-- The splitting chart of the descended middle exterior matrix algebra. -/
abbrev middleExteriorSplittingChart :
    M ⊗[K] c.middleExteriorCSA ≃ₐ[M]
      Matrix (MiddleExteriorIndices m) (MiddleExteriorIndices m) M :=
  matrixFixedSplittingChart c.middleExteriorAction

variable [Normal K F] [Algebra.IsQuadraticExtension K F]

/-- The discriminant class in the matrix chart of the descended unitary algebra. -/
abbrev chartDiscriminantClass : BrauerGroup.{u, u} K :=
  discriminantClass c.restrictNormal_ne_one c.isUnitary c.action.descentEquiv

private theorem middleExterior_relativeClass :
    BrauerComparison.relativeClass c.middleExteriorSplittingChart =
      relativeDiscriminantClass c.restrictNormal_ne_one c.isUnitary c.action.descentEquiv := by
  refine (relativeClass_ofProjectiveLifts (I := MiddleExteriorIndices m)
    (middleExteriorLift m F.fixingSubgroup c.x) c.middleExteriorFactor_spec).trans ?_
  have hcenter := centerFixing_eq (K := K) (M := M) (F := F)
  have he := relativeDiscriminantClass_eq_of_lifts c.restrictNormal_ne_one c.isUnitary
    c.action.descentEquiv c.x c.exteriorFactor
    (fun g hg b => by
      rw [hcenter] at hg ⊢
      simpa only [chartMap_apply, descentEquiv_one_tmul] using
        c.twistedAct_alg_of_mem hg b)
    (fun g hg b => by
      rw [hcenter] at hg ⊢
      simpa only [chartMap_apply, descentEquiv_one_tmul,
        UnitaryTwistedDescent.coe_outerInvolution] using c.twistedAct_of_not_mem_eq hg b)
    (by simpa only [hcenter] using c.exteriorFactor_spec)
  simpa only [hcenter] using he

/-- The descended matrix algebra of the middle exterior power represents the
discriminant class of the twisted unitary algebra. -/
theorem middleExteriorCSA_classOf (S : Type u) [Field S] [Algebra K S]
    [IsSepClosure K S] [Algebra M S] [IsScalarTower K M S] :
    Brauer.classOf c.middleExteriorCSA = c.chartDiscriminantClass := by
  apply (BrauerComparison.brauerContinuousEquiv K S).injective
  rw [BrauerComparison.brauerContinuousEquiv_at_chart K S _ M c.middleExteriorSplittingChart,
    chartDiscriminantClass, brauerContinuousEquiv_discriminantClass,
    c.middleExterior_relativeClass]

end Langlands.LinearAlgebra.UnitaryTwistedChart.Cocycle
