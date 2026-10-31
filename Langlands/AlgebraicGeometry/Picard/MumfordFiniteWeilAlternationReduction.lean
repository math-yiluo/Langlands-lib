import Langlands.AlgebraicGeometry.Picard.MumfordFiniteWeilAlternationStatement
import Langlands.AlgebraicGeometry.Picard.FiniteWeilBaseChange
import Langlands.AbelianScheme.KernelTranslationSectionFormula

/-! # Reduction of Mumford alternation to a trivialization with equal point restrictions -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (square : MumfordBundlePicardZeroStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] (A : AbelianScheme S)
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (L : LineBundle A.X.left) (B : LineBundle S)
  (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅
    structureSheaf S)
  (M : LineBundle A.X.left)
  (evaluation : tensorObj (LineBundle.normalize preservation A.X.hom (unitSection A)
    (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left)

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

/-- The Mumford family pulled back to the parameter `T` along a point `x` of `A[n]`, as a
module on `T ×_S A`. -/
abbrev mumfordKernelPointModule (n : ℕ) {T : Over S}
    (x : T ⟶ (GroupScheme.kernel (groupHom (multiplication A (n : ℤ)))).X) :
    ((relativeSpace A.X.hom).obj T).Modules :=
  (Scheme.Modules.pullback ((relativeSpace A.X.hom).map
    (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom))).obj
      (mumfordFamilyOfLineBundle preservation A L B evaluationB M evaluation).obj.carrier

/-- The geometric input: the pulled-back Mumford module has a trivialization of its
`[n]`-pullback whose restrictions along the unit section `e` and along its translate by
`x` agree under the canonical identification. -/
def MumfordKernelPointTrivialization (n : ℕ) {T : Over S}
    (x : T ⟶ (GroupScheme.kernel (groupHom (multiplication A (n : ℤ)))).X) : Prop :=
  ∃ α : (Scheme.Modules.pullback ((homFamilySpaceMap (multiplication A (n : ℤ))).app T)).obj
      (mumfordKernelPointModule preservation A L B evaluationB M evaluation n x) ≅
        structureModule ((relativeSpace A.X.hom).obj T),
    equalCompositeUnitAut ((homFamilySpaceMap (multiplication A (n : ℤ))).app T)
      ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)
      ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
        kernelShear (multiplication A (n : ℤ)) (𝟙 T) x)
      (by rw [Category.assoc, kernelShear_homFamilySpaceMap,
        CategoryTheory.Functor.map_id, Category.id_comp]) α = Iso.refl _

/-- Given the geometric input at a point `x` of `A[n]`, the finite pairing along a Mumford
homomorphism takes the value `1` at `(x, x)`. -/
theorem finiteWeilAlongHomValue_self_eq_one_of_trivialization
    (lam : A ⟶ DA)
    (hlam : (groupHom lam).hom.hom =
      mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA)
    (n : ℕ) {T : Over S}
    (x : T ⟶ (kernelCommGroupScheme (multiplication A (n : ℤ))).X)
    (hx : MumfordKernelPointTrivialization preservation A L B evaluationB M evaluation n x) :
    finiteWeilAlongHomValue preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA lam n x x = 1 := by
  obtain ⟨α, hα⟩ := hx
  unfold finiteWeilAlongHomValue
  set y := x ≫ finiteWeilAlongHomTorsionMap preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA lam n with hy
  have hp : y ≫ (GroupScheme.torsionι (Langlands.CommGroupScheme.toGrp
      (dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA stability composition
        unitCoherence associativity comparison symmetry)) (n : ℤ)).hom.hom =
      (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom) ≫
        mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA := by
    have ht := finiteWeilAlongHom_torsion_inclusion preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA lam n
    rw [hy, Category.assoc]
    refine (congrArg (x ≫ ·) ht).trans ?_
    rw [Category.assoc, hlam]
  let F := (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
    (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom)).obj
      (mumfordFamilyOfLineBundle preservation A L B evaluationB M evaluation)
  have hF : HasTrivialHomPullback (multiplication A (n : ℤ)) T
      ((RigidifiedLineBundle.forget _).obj F) := ⟨α⟩
  have hclass : RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) F =
      (dualPointClass stability A hA (y ≫ (GroupScheme.torsionι
        (Langlands.CommGroupScheme.toGrp (dualCommGroupSchemeFromEvaluation A hA preservation
          MA evaluationA stability composition unitCoherence associativity comparison
          symmetry)) (n : ℤ)).hom.hom)).val := by
    rw [← dualPointFamily_class, hp]
    exact (mumfordSchemeMapOfLineBundle_points preservation A L B evaluationB M evaluation
      square hA T _).symm
  have hz : (1 : T ⟶ (mu S n).X) ≫ (mu.incl S n).toMul.hom.hom =
      Cartier.characterEvaluation
        (dualTorsionCharacter preservation composition unitCoherence associativity comparison
          symmetry stability hA MA evaluationA n y) x := by
    rw [dualTorsionCharacter_eq_dualKernelCharacter A preservation composition unitCoherence
        associativity comparison symmetry stability hA MA evaluationA n y
        (torsion_dualSchemeMap_eq_origin A preservation composition unitCoherence associativity
          comparison symmetry stability hA MA evaluationA n y),
      dualKernelCharacter_eq_of_family_class hA stability (multiplication A (n : ℤ)) hA _ _ F hF
        hclass,
      trivialHomPullbackCharacter_eq (multiplication A (n : ℤ)) (universalGlobalFunctions A)
        _ hF α,
      characterEvaluation_intrinsicKernelCharacter_eq_one (multiplication A (n : ℤ)) α
        (universalGlobalFunctions A) x
        (kernelTranslationUnit_eq_one_of_section (multiplication A (n : ℤ)) α
          (universalGlobalFunctions A) x hα)]
    simp
  exact (finiteWeilValue_unique preservation composition unitCoherence associativity comparison
    symmetry stability hA MA evaluationA n x y 1 hz).symm

/-- Conditional form of the target: if the geometric input holds for the universal point of
`A[n]`, the finite pairing along a Mumford homomorphism is trivial on the diagonal. -/
theorem mumfordFiniteWeil_diagonal_of_trivialization
    (lam : A ⟶ DA)
    (hlam : (groupHom lam).hom.hom =
      mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA)
    (n : ℕ)
    (hx : MumfordKernelPointTrivialization preservation A L B evaluationB M evaluation n
      (𝟙 (kernelCommGroupScheme (multiplication A (n : ℤ))).X)) :
    prod.lift (𝟙 _) (𝟙 _) ≫
        finiteWeilAlongHomPairing preservation composition unitCoherence associativity
          comparison symmetry stability hA geometryA MA evaluationA lam n =
      (1 : (kernelCommGroupScheme (multiplication A (n : ℤ))).X ⟶ (mu S n).X) := by
  rw [finiteWeilAlongHomPairing_points]
  exact finiteWeilAlongHomValue_self_eq_one_of_trivialization preservation square composition
    unitCoherence associativity comparison symmetry stability A hA geometryA MA evaluationA
    L B evaluationB M evaluation lam hlam n _ hx

end Langlands.AbelianScheme
