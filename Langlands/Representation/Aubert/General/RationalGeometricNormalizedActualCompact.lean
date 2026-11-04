import Langlands.Representation.Aubert.General.RationalGeometricNormalizedEndpointCoefficient
import Langlands.Representation.Aubert.General.RationalGeometricNormalizedCompactFunctor

/-! # The actual normalized geometric coefficient under compact induction -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Induction
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (I J : Finset (SimpleRoot i ν))
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  [TopologicalSpace (RationalPoint k G.X)]
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hM : ∀ H, IsClosed (levi i ν H : Set (RationalPoint k G.X)))
  (hU : ∀ H, IsClosed (unipotent i ν H : Set (RationalPoint k G.X)))
  (hSource : GeometricSourceDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  (hTarget : GeometricTargetDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hpJ : Continuous dJ.projection)

local notation "A" => RationalPoint k G.X
local notation "PI" => parabolic i ν I
local notation "MI" => levi i ν I
local notation "UI" => unipotent i ν I
local notation "PJ" => parabolic i ν J
local notation "MJ" => levi i ν J
local notation "UJ" => unipotent i ν J
local notation "Lt" => Subgroup.subgroupOf (geometricTargetIntersection MI MJ (n : A)) MI
local notation "K" => Subgroup.subgroupOf (geometricTargetIntersection MI PJ (n : A)) MI
local notation "S" => Subgroup.subgroupOf (geometricSourceIntersection UI MJ (n : A)) MJ
local notation "Ls" => Subgroup.subgroupOf (geometricSourceIntersection MI MJ (n : A)) MJ
local notation "ε₁" => geometricEpsilonOne i ν I J dI dJ n (hU J) hPI
local notation "ε₂" => geometricEpsilonTwo i ν I J dI dJ n (hU I) hPJ
local notation "ε" => MonoidHom.comp (ε₁ * ε₂) hTarget.projection

include hpJ in
/-- Both original epsilon corrections, inflated to the entire target
intersection through its actual Levi projection, have open kernel. -/
theorem isOpen_ker_geometricInflatedEpsilonProduct :
    IsOpen ((ε).ker : Set K) := by
  have hprod : IsOpen (((ε₁ * ε₂).ker : Subgroup Lt) : Set Lt) := by
    apply Subgroup.isOpen_mono (H₁ := (ε₁).ker ⊓ (ε₂).ker)
    · intro l hl
      change ε₁ l * ε₂ l = 1
      rw [hl.1, hl.2, mul_one]
    · exact (isOpen_ker_geometricEpsilonOne i ν I J dI dJ n (hU J) hPI).inter
        (isOpen_ker_geometricEpsilonTwo i ν I J dI dJ n (hU I) hPJ)
  exact hprod.preimage
    (continuous_geometricTargetProjection PI MI UI PJ MJ UJ dI dJ (n : A)
      hTarget hpJ)

/-- The original epsilon product as a smooth character on the literal
target intersection. Neither epsilon is cancelled. -/
def geometricInflatedEpsilonProductSmoothCharacter : SmoothCharacter ℂ K where
  toMonoidHom := ε
  isOpen_ker := isOpen_ker_geometricInflatedEpsilonProduct
    i ν I J dI dJ n hU hTarget hPJ hPI hpJ

/-- Compact induction of the actual normalized geometric-term inducing
representation, with both original epsilon corrections still present. -/
def geometricTermEpsilonCompactFunctor :
    SmoothRep.{0,u,uV} ℂ MJ ⥤ SmoothRep.{0,u,max u uV} ℂ MI :=
  geometricTermInducingFunctor
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J (n : A) hSource hTarget ⋙
      (geometricInflatedEpsilonProductSmoothCharacter
        i ν I J dI dJ n hU hTarget hPJ hPI hpJ).twistFunctor ⋙
          compactInductionFunctor K

variable
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  [SecondCountableTopology (RationalPoint k G.X)]
  (hUJc : Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν J))
  (hpI : Continuous dI.projection)

/-- Compact induction lifts the actual class-preserving coefficient
equivalence, retaining the original epsilon product on the target. -/
def geometricNormalizedCompactActualTargetIso (σ : SmoothRep.{0,u,uV} ℂ MJ) :
    (geometricNormalizedCompactTargetFunctor
      i ν I J dI dJ n (hU I) (hU J) hPJ hSource hTarget).obj σ ≅
        (geometricTermEpsilonCompactFunctor
          i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hpJ).obj σ :=
  SmoothRep.mkIso (compactInducedEquiv K
    (geometricNormalizedCompactActualCoefficientEquiv
      i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hStandard hG hi hν hN
        hUJc hpI hpJ σ))

/-- The lifted coefficient comparison is pointwise the original coefficient
equivalence on the value of the same compact function. -/
@[simp] theorem geometricNormalizedCompactActualTargetIso_eval
    (σ : SmoothRep.{0,u,uV} ℂ MJ)
    (F : CompactFunctions K (geometricNormalizedCompactCoefficient
      i ν I J dI dJ n (hU I) (hU J) hPJ hSource hTarget σ.representation))
    (l : MI) :
    eval K (twist ε (geometricTermActualCoefficient
        i ν I J n hM hU hSource hTarget σ))
      (SmoothRep.hom (geometricNormalizedCompactActualTargetIso
        i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hpJ
          hStandard hG hi hν hN hUJc hpI σ).hom F).val l =
      geometricNormalizedCompactActualCoefficientEquiv
        i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hStandard hG hi hν hN
          hUJc hpI hpJ σ
          (eval K (geometricNormalizedCompactCoefficient
            i ν I J dI dJ n (hU I) (hU J) hPJ hSource hTarget σ.representation)
              F.val l) := by
  rfl

/-- The original compact target is naturally compact induction of the
actual inducing functor, twisted by both original epsilon corrections. -/
def geometricNormalizedCompactActualTargetNatIso :
    geometricNormalizedCompactTargetFunctor
      i ν I J dI dJ n (hU I) (hU J) hPJ hSource hTarget ≅
        geometricTermEpsilonCompactFunctor
          i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hpJ :=
  NatIso.ofComponents
    (geometricNormalizedCompactActualTargetIso
      i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hpJ
        hStandard hG hi hν hN hUJc hpI)
    (by
      intro σ τ a
      ext F
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      funext l
      exact geometricNormalizedCompactActualCoefficientEquiv_natural
        i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hStandard hG hi hν hN
          hUJc hpI hpJ a
          (eval K (geometricNormalizedCompactCoefficient
            i ν I J dI dJ n (hU I) (hU J) hPJ hSource hTarget σ.representation)
              F.val l))

variable [T2Space (RationalPoint k G.X)]
  (hUIc : Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))

/-- The actual original normalized compact orbit quotient is naturally
compact induction of the actual normalized geometric-term coefficient,
with both epsilon corrections retained. -/
def geometricNormalizedCompactActualNatIso :
    geometricNormalizedCompactSourceFunctor
      i ν I J dI dJ n (hU I) (hU J) hPJ hSource hTarget
        hPI (hM I) (hM J) hUIc hStandard hG hi hν hN hpI hpJ ≅
      geometricTermEpsilonCompactFunctor
        i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hpJ :=
  (geometricNormalizedCompactNatIso
    i ν I J dI dJ n (hU I) (hU J) hPJ hSource hTarget
      hPI (hM I) (hM J) hUIc hStandard hG hi hν hN hpI hpJ) ≪≫
        geometricNormalizedCompactActualTargetNatIso
          i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hpJ
            hStandard hG hi hν hN hUJc hpI

end Langlands.Aubert.General.RationalPointFamily
