import Langlands.AbelianScheme.Tate.WeilBaseChange
import Langlands.AbelianScheme.Tate.WeilRationalAlongHom
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChange
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeProof

/-! # Ground base change of Weil pairings along actual homomorphisms -/

universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
noncomputable section

namespace Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (hA' : HasDualScheme ((baseChange b).obj A))
  (geometryA' : DualSchemeGeometry ((baseChange b).obj A) hA')
  (MA' : LineBundle ((relativeSpace ((baseChange b).obj A).X.hom).obj
    (dualScheme ((baseChange b).obj A) hA')))
  (evaluationA' : tensorObj (poincareFamily ((baseChange b).obj A) hA').obj.carrier
    MA'.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj A).X.hom).obj
      (dualScheme ((baseChange b).obj A) hA')))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
set_option quotPrecheck false in
local notation "DAb" => dualAbelianSchemeFromEvaluation ((baseChange b).obj A) hA'
  geometryA' preservation MA' evaluationA' stability composition unitCoherence associativity
  comparison symmetry
local notation "E" => dualGrpBaseChangeIso b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA MA evaluationA hA' MA' evaluationA'
local notation "EA" => dualAbelianBaseChangeIso preservation stability composition unitCoherence
  associativity comparison symmetry universality dualAbelianBaseChange b A hA geometryA MA
  evaluationA hA' geometryA' MA' evaluationA'
/-- Base change an actual dual-valued homomorphism using the published theorem
that the canonical dual comparison respects the group structure. -/
def canonicalDualValuedBaseChange (lam : A ⟶ DA) : (baseChange b).obj A ⟶ DAb :=
  dualAbelianBaseChangeMap preservation stability composition unitCoherence associativity
    comparison symmetry universality dualAbelianBaseChange b A hA geometryA MA evaluationA
    hA' geometryA' MA' evaluationA' lam

local notation "lamBC" => canonicalDualValuedBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA
  evaluationA hA' geometryA' MA' evaluationA'
local notation "dualLevel" => dualLevelBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA MA evaluationA hA' MA' evaluationA'
local notation "dualIntegral" => dualIntegralBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA MA evaluationA
  hA' MA' evaluationA'
local notation "dualRational" => dualRationalBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA MA evaluationA
  hA' MA' evaluationA'

/-- The existing canonical abelian comparison lifts exactly the group comparison
used by the dual torsion and Tate comparisons. -/
theorem groupHom_dualAbelianBaseChangeIso : groupHom (EA).hom = (E).hom := by
  apply Grp.hom_ext
  exact dualAbelianBaseChangeIso_hom preservation stability composition unitCoherence
    associativity comparison symmetry universality dualAbelianBaseChange b A hA geometryA
    MA evaluationA hA' geometryA' MA' evaluationA'

variable (T : Over S')

/-- Canonical comparison of the target makes the actual finite homomorphism square commute. -/
theorem dualLevelBaseChange_canonicalDualValuedBaseChange (lam : A ⟶ DA) (n : ℕ)
    (y : GroupScheme.Tate.Level ((baseChange b).obj A).toGrp T n) :
    dualLevel T n (GroupScheme.Tate.levelMap T (groupHom (lamBC lam)) n y) =
      GroupScheme.Tate.levelMap ((Over.map b).obj T) (groupHom lam) n
        (GroupScheme.Tate.levelBaseChange b A.toGrp T n y) := by
  have he : groupHom (lamBC lam) =
      (Over.pullback b).mapGrp.map (groupHom lam) ≫ (E).hom := by
    change (Over.pullback b).mapGrp.map (groupHom lam) ≫ groupHom (EA).hom = _
    rw [groupHom_dualAbelianBaseChangeIso]
  change GroupScheme.Tate.levelBaseChange b (DA).toGrp T n
      (GroupScheme.Tate.levelMap T (E).inv n
        (GroupScheme.Tate.levelMap T (groupHom (lamBC lam)) n y)) = _
  rw [he]
  have hc : GroupScheme.Tate.levelMap T (E).inv n
      (GroupScheme.Tate.levelMap T
        ((Over.pullback b).mapGrp.map (groupHom lam) ≫ (E).hom) n y) =
      GroupScheme.Tate.levelMap T ((Over.pullback b).mapGrp.map (groupHom lam)) n y := by
    apply GroupScheme.Tate.toSection_injective
    change (Additive.toMul y).val ≫
      (((Over.pullback b).mapGrp.map (groupHom lam) ≫ (E).hom) ≫ (E).inv).hom.hom = _
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  exact (congrArg (GroupScheme.Tate.levelBaseChange b (DA).toGrp T n) hc).trans
    (GroupScheme.Tate.levelBaseChange_map b T (groupHom lam) n y)

/-- The actual integral Tate map of the base-changed homomorphism has the same square. -/
theorem dualIntegralBaseChange_canonicalDualValuedBaseChange (lam : A ⟶ DA) (P : ℕ → Prop)
    (y : GroupScheme.Tate.Integral ((baseChange b).obj A).toGrp T P) :
    dualIntegral T P (GroupScheme.Tate.map T P (groupHom (lamBC lam)) y) =
      GroupScheme.Tate.map ((Over.map b).obj T) P (groupHom lam)
        (GroupScheme.Tate.integralBaseChange b A.toGrp T P y) := by
  apply Subtype.ext
  funext n
  exact dualLevelBaseChange_canonicalDualValuedBaseChange b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' T lam n.val (y.val n)

/-- Rationalization over the integers preserves the canonical dual-valued map square. -/
theorem dualRationalBaseChange_canonicalDualValuedBaseChange (lam : A ⟶ DA) (P : ℕ → Prop)
    (y : GroupScheme.Tate.Rational ((baseChange b).obj A).toGrp T P) :
    dualRational T P (GroupScheme.Tate.rationalMap T P (groupHom (lamBC lam)) y) =
      GroupScheme.Tate.rationalMap ((Over.map b).obj T) P (groupHom lam)
        (GroupScheme.Tate.rationalBaseChange b A.toGrp T P y) := by
  induction y using TensorProduct.inductionOn with
  | tmul q y =>
    change q ⊗ₜ[ℤ] dualIntegral T P (GroupScheme.Tate.map T P (groupHom (lamBC lam)) y) =
      q ⊗ₜ[ℤ] GroupScheme.Tate.map ((Over.map b).obj T) P (groupHom lam)
        (GroupScheme.Tate.integralBaseChange b A.toGrp T P y)
    exact congrArg (fun z => q ⊗ₜ[ℤ] z)
      (dualIntegralBaseChange_canonicalDualValuedBaseChange b A preservation composition
        unitCoherence associativity comparison symmetry stability universality hA geometryA
        MA evaluationA hA' geometryA' MA' evaluationA' T lam P y)
  | add y z hy hz => simp only [map_add, hy, hz]

variable [QuasiSeparatedSpace S] [QuasiSeparatedSpace S']
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})

/-- The finite pulled-back Weil value commutes with ground base change. -/
theorem finiteWeilLevelAlongHom_baseChange (lam : A ⟶ DA) (n : ℕ)
    (x y : GroupScheme.Tate.Level ((baseChange b).obj A).toGrp T n) :
    finiteWeilLevelBilinearMap preservation composition unitCoherence associativity comparison
        symmetry stability hA' MA' evaluationA' n T x
        (GroupScheme.Tate.levelMap T (groupHom (lamBC lam)) n y) =
      finiteWeilLevelBilinearMap preservation composition unitCoherence associativity comparison
        symmetry stability hA MA evaluationA n ((Over.map b).obj T)
        (GroupScheme.Tate.levelBaseChange b A.toGrp T n x)
        (GroupScheme.Tate.levelMap ((Over.map b).obj T) (groupHom lam) n
          (GroupScheme.Tate.levelBaseChange b A.toGrp T n y)) := by
  rw [finiteWeilLevelBilinearMap_baseChange b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA MA evaluationA hA' MA'
    evaluationA']
  rw [dualLevelBaseChange_canonicalDualValuedBaseChange]

/-- Base change preserves the actual integral pairing pulled back in the second variable. -/
theorem integralWeilAlongHomBilinearMap_baseChange (lam : A ⟶ DA) (P : ℕ → Prop)
    (x y : GroupScheme.Tate.Integral ((baseChange b).obj A).toGrp T P) :
    integralWeilAlongHomBilinearMap preservation composition unitCoherence associativity
        comparison symmetry stability hA' geometryA' MA' evaluationA' compatibility T
        (lamBC lam) P x y =
      integralWeilAlongHomBilinearMap preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA compatibility
        ((Over.map b).obj T) lam P
        (GroupScheme.Tate.integralBaseChange b A.toGrp T P x)
        (GroupScheme.Tate.integralBaseChange b A.toGrp T P y) := by
  change integralWeilValue preservation composition unitCoherence associativity comparison
      symmetry stability hA' MA' evaluationA' compatibility T P x
      (GroupScheme.Tate.map T P (groupHom (lamBC lam)) y) =
    integralWeilValue preservation composition unitCoherence associativity comparison symmetry
      stability hA MA evaluationA compatibility ((Over.map b).obj T) P
      (GroupScheme.Tate.integralBaseChange b A.toGrp T P x)
      (GroupScheme.Tate.map ((Over.map b).obj T) P (groupHom lam)
        (GroupScheme.Tate.integralBaseChange b A.toGrp T P y))
  rw [integralWeilValue_baseChange b A preservation composition unitCoherence associativity
    comparison symmetry stability universality hA MA evaluationA hA' MA' evaluationA']
  rw [dualIntegralBaseChange_canonicalDualValuedBaseChange]

/-- Rational base change preserves the actual twist-valued pullback Weil pairing. -/
theorem rationalWeilAlongHomBilinearMap_baseChange (lam : A ⟶ DA) (P : ℕ → Prop)
    (x y : GroupScheme.Tate.Rational ((baseChange b).obj A).toGrp T P) :
    rationalWeilAlongHomBilinearMap preservation composition unitCoherence associativity
        comparison symmetry stability hA' geometryA' MA' evaluationA' compatibility T
        (lamBC lam) P x y =
      rationalWeilAlongHomBilinearMap preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA compatibility
        ((Over.map b).obj T) lam P
        (GroupScheme.Tate.rationalBaseChange b A.toGrp T P x)
        (GroupScheme.Tate.rationalBaseChange b A.toGrp T P y) := by
  simp only [rationalWeilAlongHomBilinearMap_apply]
  rw [rationalWeilBilinearMap_baseChange b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA MA evaluationA hA' MA'
    evaluationA']
  rw [dualRationalBaseChange_canonicalDualValuedBaseChange]

/-- The adelic equation uses the same scalar comparison on both modules and the twist. -/
theorem adelicWeilAlongHomBilinearMap_baseChange (lam : A ⟶ DA) (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (x y : GroupScheme.Tate.Rational ((baseChange b).obj A).toGrp T P) :
    adelicWeilAlongHomBilinearMap preservation composition unitCoherence associativity
        comparison symmetry stability hA' geometryA' MA' evaluationA' compatibility T
        (lamBC lam) P h x y =
      adelicWeilAlongHomBilinearMap preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA compatibility
        ((Over.map b).obj T) lam P h
        (GroupScheme.Tate.finiteAdeleBaseChange b A.toGrp T P h x)
        (GroupScheme.Tate.finiteAdeleBaseChange b A.toGrp T P h y) := by
  simp only [adelicWeilAlongHomBilinearMap_apply]
  exact rationalWeilAlongHomBilinearMap_baseChange b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA geometryA MA evaluationA
    hA' geometryA' MA' evaluationA' T compatibility lam P x y

/-- Away adelic base change shares the coupled scalar comparison at both endpoints. -/
theorem awayAdelicWeilAlongHomBilinearMap_baseChange (lam : A ⟶ DA)
    {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
    (x y : GroupScheme.Tate.RationalAway ((baseChange b).obj A).toGrp T m) :
    awayAdelicWeilAlongHomBilinearMap preservation composition unitCoherence associativity
        comparison symmetry stability hA' geometryA' MA' evaluationA' compatibility T
        (lamBC lam) hAway x y =
      awayAdelicWeilAlongHomBilinearMap preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA compatibility
        ((Over.map b).obj T) lam hAway
        (GroupScheme.Tate.primeToFiniteAdeleBaseChange b A.toGrp T hAway x)
        (GroupScheme.Tate.primeToFiniteAdeleBaseChange b A.toGrp T hAway y) := by
  simp only [awayAdelicWeilAlongHomBilinearMap_apply]
  exact rationalWeilAlongHomBilinearMap_baseChange b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA geometryA MA evaluationA
    hA' geometryA' MA' evaluationA' T compatibility lam (fun n => Nat.Coprime n m) x y

end Langlands.AbelianScheme
