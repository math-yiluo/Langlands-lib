import Langlands.AlgebraicGeometry.Picard.SmoothFamilyAlgebraicTriviality
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldTranslationDifferenceLiftingStatement
import Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroReduction
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceStatement
import Langlands.AbelianScheme.SmoothGeometricIntegralityStatement

/-! # Translation-invariant bundles are algebraically trivial via a smooth family

Over an algebraically closed field, a translation-invariant line bundle `L` on an
abelian variety `A` is `t_x^*H ⊗ H⁻¹` for an ample `H` (Proposition (7.21) of
Edixhoven, van der Geer and Moonen). The family `μ^*H ⊗ pr₂^*H⁻¹` on `A ×_K A`,
parametrized by the first factor, restricts to `H ⊗ H⁻¹` at the identity and to
`t_x^*H ⊗ H⁻¹` at `x`. The three geometric inputs are explicit hypotheses. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme.SmoothFamilyOfTranslation

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AbelianScheme.MumfordPicardZero (pullbackTensorIso pullbackCompIso tensorIsoOf)

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- Restricting addition `A ×_S A → A` to the fibre over a section `c` of the
parameter factor is translation by `c`. -/
lemma pointMap_addition (c : Over.mk (𝟙 S) ⟶ A.X) :
    smoothFamilyPointMap A A.X c ≫ mumfordAddition A =
      (GroupScheme.translation A.toGrp c).left := by
  let φ : A.X ⟶ mumfordProduct A := Over.homMk (smoothFamilyPointMap A A.X c) (by
    change smoothFamilyPointMap A A.X c ≫ pullback.fst A.X.hom A.X.hom ≫ A.X.hom = _
    rw [← Category.assoc, smoothFamilyPointMap_fst, Category.assoc, Over.w c]
    simp)
  have key : φ ≫ (mumfordFirst A * mumfordSecond A) =
      GroupScheme.translation A.toGrp c := by
    rw [MonObj.comp_mul, GroupScheme.translation]
    congr 1
    · apply Over.OverMorphism.ext
      simp [φ, mumfordFirst]
    · apply Over.OverMorphism.ext
      simp [φ, mumfordSecond]
  exact congrArg CommaMorphism.left key

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

/-- The family `μ^*H ⊗ pr₂^*N` on the parameter-first product `A ×_S A`. -/
def family (H N : LineBundle A.X.left) : LineBundle ((relativeSpace A.X.hom).obj A.X) :=
  LineBundle.tensor preservation
    ((LineBundle.pullback (mumfordAddition A)).obj H)
    ((LineBundle.pullback (pullback.snd A.X.hom A.X.hom)).obj N)

/-- The restriction of the family to the fibre over `c` is `t_c^*H ⊗ N`. -/
def familyRestrictionIso (H N : LineBundle A.X.left) (c : Over.mk (𝟙 S) ⟶ A.X) :
    (LineBundle.pullback (smoothFamilyPointMap A A.X c)).obj (family A preservation H N) ≅
      LineBundle.tensor preservation
        ((LineBundle.pullback (GroupScheme.translation A.toGrp c).left).obj H) N :=
  ObjectProperty.isoMk _
    (pullbackTensorIso preservation (smoothFamilyPointMap A A.X c) _ _ ≪≫
      tensorIsoOf
        (pullbackCompIso _ _ _ (pointMap_addition A c) H.obj).symm
        ((pullbackCompIso _ _ _ (smoothFamilyPointMap_snd A A.X c) N.obj).symm ≪≫
          (Scheme.Modules.pullbackId _).app N.obj))

/-- At the identity section the restriction is `H ⊗ N`, trivialized by `evaluation`. -/
def familyRestrictionOneIso (H N : LineBundle A.X.left)
    (evaluation : tensorObj H.obj N.obj ≅ structureSheaf A.X.left) :
    (LineBundle.pullback (smoothFamilyPointMap A A.X 1)).obj (family A preservation H N) ≅
      LineBundle.trivial A.X.left :=
  familyRestrictionIso A preservation H N 1 ≪≫
    ObjectProperty.isoMk _
      (tensorIsoOf
        ((Scheme.Modules.pullbackCongr (by simp)).app H.obj ≪≫
          (Scheme.Modules.pullbackId _).app H.obj)
        (Iso.refl _) ≪≫ evaluation)

end Langlands.AbelianScheme.SmoothFamilyOfTranslation

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- Translation invariance implies algebraic triviality via a smooth family, given
geometric integrality of smooth geometrically connected schemes, an ample bundle on
every abelian variety over an algebraically closed field, and Proposition (7.21). -/
theorem isAlgebraicallyTrivialViaSmoothFamily_of_isTranslationInvariant
    (integrality : SmoothGeometricIntegrality.{u})
    (ample : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u})
    (lifting : AlgClosedFieldTranslationDifferenceLiftingStatement.{u})
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (L : LineBundle A.X.left)
    (hL : GroupScheme.IsTranslationInvariant A.toGrp L) :
    IsAlgebraicallyTrivialViaSmoothFamily A L := by
  let preservation : pullbackTensorComparisonIsIsoStatement.{u} := pullbackTensorComparisonIsIso
  obtain ⟨H, hH⟩ := ample K A.toGrp inferInstance inferInstance inferInstance
  obtain ⟨N, ⟨evaluation⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf H
  obtain ⟨x, ⟨e⟩⟩ := lifting preservation K A H N evaluation L hH hL
  refine ⟨A.X, inferInstance, inferInstance, inferInstance, inferInstance,
    integrality K A.X.left A.X.hom inferInstance inferInstance, 1, x,
    SmoothFamilyOfTranslation.family A preservation H N,
    ⟨SmoothFamilyOfTranslation.familyRestrictionOneIso A preservation H N evaluation⟩,
    ⟨SmoothFamilyOfTranslation.familyRestrictionIso A preservation H N x ≪≫ e⟩⟩

end Langlands.AbelianScheme
