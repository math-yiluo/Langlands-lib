import Langlands.AbelianScheme.PolarizedFiniteLevel.Pullback
import Langlands.AlgebraicGeometry.Picard.PolarizationDiagonalMumfordStatement
import Langlands.AlgebraicGeometry.Picard.PoincareSliceSymmetryBaseChange
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms

/-! # The canonical cubic bundle of ordinary polarized finite-level data -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

@[reassoc]
private lemma diagonalParameterMap_fst {S : Scheme.{u}} (A : AbelianScheme S)
    (hA : HasDualScheme A) (f : A.X ⟶ dualScheme A hA) :
    (relativeDiagonal A ≫ (relativeSpace A.X.hom).map f) ≫
        pullback.fst (dualScheme A hA).hom A.X.hom = f.left := by
  simp only [relativeDiagonal, relativeSpace, Functor.comp_map, Over.forget_map,
    Over.pullback_map_left, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
    Category.id_comp]

@[reassoc]
private lemma diagonalParameterMap_snd {S : Scheme.{u}} (A : AbelianScheme S)
    (hA : HasDualScheme A) (f : A.X ⟶ dualScheme A hA) :
    (relativeDiagonal A ≫ (relativeSpace A.X.hom).map f) ≫
        pullback.snd (dualScheme A hA).hom A.X.hom = 𝟙 A.X.left := by
  simp only [relativeDiagonal, relativeSpace, Functor.comp_map, Over.forget_map,
    Over.pullback_map_left, Category.assoc, pullback.lift_snd]

/-- The diagonal Poincaré line bundle commutes with the canonical change of dual. -/
def poincareDiagonalBaseChangeIso
    (universality : PicardZeroUniversalBaseChangeStatement.{u})
    {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)
    (hA : HasDualScheme A) (f : A.X ⟶ dualScheme A hA) :
    poincareDiagonalBundle ((baseChange b).obj A)
        (hasDualScheme_baseChange universality b A hA)
        (dualBaseChangeMap A hA universality b f) ≅
      (LineBundle.pullback (pullback.fst A.X.hom b)).obj
        (poincareDiagonalBundle A hA f) := by
  change (LineBundle.pullback (relativeDiagonal ((baseChange b).obj A))).obj
      ((LineBundle.pullback ((relativeSpace ((baseChange b).obj A).X.hom).map
        (dualBaseChangeMap A hA universality b f))).obj
        ((RigidifiedLineBundle.forget _).obj
          (poincareFamily ((baseChange b).obj A)
            (hasDualScheme_baseChange universality b A hA)))) ≅ _
  refine (LineBundle.pullbackComp _ _).app _ ≪≫
    baseChangePoincarePullbackIso universality b A hA _
      (pullback.fst A.X.hom b ≫ relativeDiagonal A ≫ (relativeSpace A.X.hom).map f) ?_ ?_ ≪≫
    ((LineBundle.pullbackComp _ _).app _).symm ≪≫
    (LineBundle.pullback _).mapIso ((LineBundle.pullbackComp _ _).app _).symm
  · erw [← Category.assoc, diagonalParameterMap_fst]
    rw [Category.assoc, diagonalParameterMap_fst]
    exact dualBaseChangeMap_left_inv_fst universality b A hA f
  · erw [← Category.assoc, diagonalParameterMap_snd]
    rw [Category.assoc, diagonalParameterMap_snd]
    erw [Category.id_comp]

namespace PolarizedFiniteLevel

variable {P : Prerequisites.{u}} {S S' : Scheme.{u}} {g d n : ℕ}

/-- The actual diagonal Poincaré bundle attached to the datum's polarization. -/
def Datum.canonicalBundle (a : Datum P S g d n) : LineBundle a.abelian.X.left :=
  poincareDiagonalBundle a.abelian a.dualWitness.hasDual
    (a.dualWitness.parameterMap P a.polarization)

/-- The actual tensor cube used to linearly rigidify an ordinary polarized datum. -/
def Datum.cubicBundle (a : Datum P S g d n) : LineBundle a.abelian.X.left :=
  ⟨tensorPow a.canonicalBundle.obj 3,
    tensorPow_isLocallyFreeRankOne _ a.canonicalBundle 3⟩

/-- The module sheaf whose projectivization is used in linear rigidification. -/
def Datum.rigidificationModule (a : Datum P S g d n) : S.Modules :=
  (Scheme.Modules.pushforward a.abelian.X.hom).obj a.cubicBundle.obj

/-- The canonical bundle of the actual pulled-back datum is the pulled-back bundle. -/
def Datum.canonicalBundlePullbackIso (a : Datum P S g d n) (b : S' ⟶ S) :
    (a.pullback b).canonicalBundle ≅
      (LineBundle.pullback (pullback.fst a.abelian.X.hom b)).obj a.canonicalBundle := by
  change poincareDiagonalBundle ((baseChange b).obj a.abelian)
      (hasDualScheme_baseChange P.universality b a.abelian a.dualWitness.hasDual)
      ((a.dualWitness.pullback P b).parameterMap P
        (a.dualWitness.pullbackMap P b (a.dualWitness.pullback P b) a.polarization)) ≅ _
  rw [DualWitness.parameterMap_pullbackMap]
  exact poincareDiagonalBaseChangeIso P.universality b a.abelian a.dualWitness.hasDual
    (a.dualWitness.parameterMap P a.polarization)

/-- The cubic bundle of the actual pulled-back datum is the pulled-back cubic bundle. -/
def Datum.cubicBundlePullbackIso (a : Datum P S g d n) (b : S' ⟶ S) :
    (a.pullback b).cubicBundle ≅
      (LineBundle.pullback (pullback.fst a.abelian.X.hom b)).obj a.cubicBundle :=
  ObjectProperty.isoMk _
    (tensorPowIso ((LineBundle.forget _).mapIso (a.canonicalBundlePullbackIso b)) 3 ≪≫
      (actualPullbackTensorPowIso (pullback.fst a.abelian.X.hom b)
        a.canonicalBundle.obj 3).symm)

end PolarizedFiniteLevel

end Langlands.AbelianScheme
