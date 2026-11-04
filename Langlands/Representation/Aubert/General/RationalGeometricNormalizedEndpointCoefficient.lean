import Langlands.Representation.Aubert.General.RationalGeometricNormalizedEndpointCharacter
import Langlands.Representation.Twist.PullbackProof

/-! # The actual normalized geometric-term inducing coefficient -/

noncomputable section

universe uI uG u uV uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General

/-- Pullback along equal homomorphisms preserves the original linear equivalence. -/
private def endpointPullbackEquiv {B C : Type uG} [Group B] [Group C]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (φ ψ : B →* C) (h : φ = ψ)
    {ρ : Representation ℂ C V} {τ : Representation ℂ C W} (e : ρ.Equiv τ) :
    Representation.Equiv (ρ.comp φ) (τ.comp ψ) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' b := by
    subst ψ
    exact e.isIntertwining' (φ b)

section Functor

variable {A : Type uG} [Group A] [TopologicalSpace A] [LocallyCompactSpace A]
  [NonarchimedeanGroup A] {Index : Type uI}
  (P M U : Finset Index → Subgroup A)
  (hM : ∀ I, IsClosed (M I : Set A)) (hU : ∀ I, IsClosed (U I : Set A))
  (I J : Finset Index) (n : A)
  (hs : GeometricSourceDecomposition P M U I J n)
  (ht : GeometricTargetDecomposition P M U I J n)

/-- The actual geometric term up to its final raw smooth induction:
normalized source Jacquet, original conjugation, target Levi inflation,
and the target positive half on the entire target parabolic intersection. -/
def geometricTermInducingFunctor :
    SmoothRep.{0,uG,uV} ℂ (M J) ⥤
      Rep.{uV} ℂ ((geometricTargetIntersection (M I) (P J) n).subgroupOf (M I)) :=
  letI := (hM I).locallyCompactSpace
  geometricSourceJacquetFunctor P M U hM hU I J n hs ⋙
    conjugationFunctor n (geometricIntersectionMembership (M I) (M J) n) ⋙
      SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv inf_le_left) ⋙
        inflationFunctor ht ⋙
          (inductionCharacter
            ((geometricTargetIntersection (M I) (U J) n).subgroupOf (M I))
            ((geometricTargetIntersection (M I) (P J) n).subgroupOf (M I))
            ((isClosed_geometricTargetIntersection (M I) (U J) (hM I) (hU J) n).preimage
              continuous_subtype_val) ht.le_normalizer).twistFunctor

/-- The published actual geometric term is precisely raw smooth induction of
this inducing coefficient functor, at its original saturated carrier universe. -/
theorem geometricTermFunctor_eq_inducing :
    geometricTermFunctor.{uI,uG,uV} P M U hM hU I J n hs ht =
      geometricTermInducingFunctor.{uI,uG,max uG uV} P M U hM hU I J n hs ht ⋙
        Induction.smoothInductionFunctor
          ((geometricTargetIntersection (M I) (P J) n).subgroupOf (M I)) := by
  rfl

end Functor

namespace RationalPointFamily

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

local notation "A" => RationalPoint k G.X
local notation "MI" => levi i ν I
local notation "UI" => unipotent i ν I
local notation "PJ" => parabolic i ν J
local notation "MJ" => levi i ν J
local notation "UJ" => unipotent i ν J
local notation "Lt0" => geometricTargetIntersection MI MJ (n : A)
local notation "Ls0" => geometricSourceIntersection MI MJ (n : A)
local notation "S" => Subgroup.subgroupOf (geometricSourceIntersection UI MJ (n : A)) MJ
local notation "Lt" => Subgroup.subgroupOf Lt0 MI
local notation "Ls" => Subgroup.subgroupOf Ls0 MJ
local notation "K" => Subgroup.subgroupOf (geometricTargetIntersection MI PJ (n : A)) MI
local notation "Rt" => Subgroup.subgroupOf (geometricTargetIntersection MI UJ (n : A)) MI
local notation "p" => geometricCoefficientLeviMap MI PJ MJ UJ (n : A) hTarget
local notation "es" => subgroupOfContinuousEquiv (inf_le_left : Ls0 ≤ MJ)
local notation "et" => subgroupOfContinuousEquiv (inf_le_left : Lt0 ≤ MI)
local notation "en" => conjugationEquiv (n : A) (geometricIntersectionMembership MI MJ (n : A))
local notation "q" => MonoidHom.comp (MulEquiv.toMonoidHom (ContinuousMulEquiv.toMulEquiv (ContinuousMulEquiv.symm es)))
  (MonoidHom.comp (MulEquiv.toMonoidHom (ContinuousMulEquiv.toMulEquiv en))
    (MonoidHom.comp (MulEquiv.toMonoidHom (ContinuousMulEquiv.toMulEquiv et)) hTarget.projection))
local notation "χs" => geometricSourceEndpointInverseHalfCharacter
  MI MJ UI (n : A) (hU I) (hM J) hSource.levi_le_normalizer
local notation "hRt" => IsClosed.preimage
  (continuous_subtype_val : Continuous (Subtype.val : MI → A))
  (isClosed_geometricTargetIntersection MI UJ (hM I) (hU J) (n : A))
local notation "χt" => HaarModulus.closedHalfCharacter Rt hRt K hTarget.le_normalizer

omit [LocallyCompactSpace (RationalPoint k G.X)] in
/-- The sequence of actual source subgroup transport, conjugation and target
Levi inflation is the original coefficient Levi map, including all nested copies. -/
theorem geometricTermCoefficientTransport_eq :
    q = p := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact (geometricIntersectionSubgroupEquiv_apply MI MJ (n : A)
    (hTarget.projection x)).symm

/-- The inducing representation obtained from the published actual source,
conjugation and target normalized induction functors. -/
abbrev geometricTermActualCoefficient (σ : SmoothRep.{0,u,uV} ℂ MJ) :=
  ((geometricTermInducingFunctor
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J (n : A) hSource hTarget).obj σ).ρ

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The same endpoint normalizations on the original ordinary Jacquet quotient,
before either original epsilon correction is cancelled. -/
abbrev geometricTermOrdinaryEndpointCoefficient (σ : Representation ℂ MJ V) :
    Representation ℂ K (Jacquet.Coinvariants σ S) :=
  letI := (hM I).locallyCompactSpace
  twist χt ((twist χs (Jacquet.action σ S Ls hSource.levi_le_normalizer)).comp p)

/-- Pullback and multiplication of the two actual endpoint twists give the
full target-intersection endpoint character on the ordinary quotient carrier. -/
theorem geometricTermOrdinaryEndpointCoefficient_eq
    (σ : Representation ℂ MJ V) :
    geometricTermOrdinaryEndpointCoefficient i ν I J n hM hU hSource hTarget σ =
      twist (geometricNormalizedCompactEndpointCharacter
        i ν I J n (hU I) (hU J) (hM I) (hM J) hSource hTarget)
        ((Jacquet.action σ S Ls hSource.levi_le_normalizer).comp p) := by
  let _ := (hM I).locallyCompactSpace
  rw [geometricTermOrdinaryEndpointCoefficient, twist_comp, twist_twist]
  rfl

/-- The actual inducing coefficient has the ordinary-Jacquet presentation.
The linear equivalence sends each trivial-localization class to the same
ordinary coinvariant class. -/
def geometricTermActualCoefficientEquiv (σ : SmoothRep.{0,u,uV} ℂ MJ) :
    Representation.Equiv
      (geometricTermActualCoefficient i ν I J n hM hU hSource hTarget σ)
      (geometricTermOrdinaryEndpointCoefficient
        i ν I J n hM hU hSource hTarget σ.representation) := by
  let _ := (hM I).locallyCompactSpace
  let _ := (hM J).locallyCompactSpace
  refine
    { toLinearEquiv := (Jacquet.Localization.trivialEquiv σ.representation S Ls
        hSource.levi_le_normalizer).toLinearEquiv
      isIntertwining' := ?_ }
  intro x
  exact (twistEquiv χt (endpointPullbackEquiv q p
    (geometricTermCoefficientTransport_eq i ν I J n hTarget)
    (twistEquiv χs
      (Jacquet.Localization.trivialEquiv σ.representation S Ls
        hSource.levi_le_normalizer)))).isIntertwining' x


@[simp] theorem geometricTermActualCoefficientEquiv_mk
    (σ : SmoothRep.{0,u,uV} ℂ MJ) (v : σ) :
    geometricTermActualCoefficientEquiv i ν I J n hM hU hSource hTarget σ
        (Jacquet.Localization.mk σ.representation S 1 v) =
      Jacquet.mk σ.representation S v := by
  rfl

@[simp] theorem geometricTermActualCoefficientEquiv_symm_mk
    (σ : SmoothRep.{0,u,uV} ℂ MJ) (v : σ) :
    (geometricTermActualCoefficientEquiv i ν I J n hM hU hSource hTarget σ).symm
        (Jacquet.mk σ.representation S v) =
      Jacquet.Localization.mk σ.representation S 1 v := by
  rfl

/-- The actual inducing functor sends a coefficient morphism to the original
map of trivial-localization classes. -/
@[simp] theorem geometricTermInducingFunctor_map_mk
    {σ τ : SmoothRep.{0,u,uV} ℂ MJ} (a : σ ⟶ τ) (v : σ) :
    ((geometricTermInducingFunctor
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J (n : A)
      hSource hTarget).map a).hom
        (Jacquet.Localization.mk σ.representation S 1 v) =
      Jacquet.Localization.mk τ.representation S 1 (SmoothRep.hom a v) := by
  rfl

/-- The ordinary quotient presentation is natural for the actual inducing
functor maps, including both endpoint normalizations. -/
theorem geometricTermActualCoefficientEquiv_natural
    {σ τ : SmoothRep.{0,u,uV} ℂ MJ} (a : σ ⟶ τ)
    (z : Jacquet.Localization.Coinvariants σ.representation S 1) :
    geometricTermActualCoefficientEquiv i ν I J n hM hU hSource hTarget τ
      (((geometricTermInducingFunctor
        (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J (n : A)
        hSource hTarget).map a).hom z) =
      Jacquet.map S Ls hSource.levi_le_normalizer (SmoothRep.hom a)
        (geometricTermActualCoefficientEquiv i ν I J n hM hU hSource hTarget σ z) := by
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective σ.representation S 1 z
  rw [geometricTermInducingFunctor_map_mk,
    geometricTermActualCoefficientEquiv_mk, geometricTermActualCoefficientEquiv_mk]
  rfl

variable
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  [SecondCountableTopology (RationalPoint k G.X)]
  (hUJc : Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν J))
  (hpI : Continuous dI.projection) (hpJ : Continuous dJ.projection)

local notation "ε" => MonoidHom.comp
  (geometricEpsilonOne i ν I J dI dJ n (hU J) hPI *
    geometricEpsilonTwo i ν I J dI dJ n (hU I) hPJ) hTarget.projection

include hStandard hG hi hν hN hUJc hpI hpJ in
/-- The normalized compact coefficient is the epsilon product twist of the
ordinary quotient with the actual source and target endpoint normalizations. -/
theorem geometricNormalizedCompactCoefficient_eq_epsilonOrdinaryEndpoints
    (σ : Representation ℂ MJ V) :
    geometricNormalizedCompactCoefficient i ν I J dI dJ n (hU I) (hU J) hPJ
        hSource hTarget σ =
      twist ε (geometricTermOrdinaryEndpointCoefficient
        i ν I J n hM hU hSource hTarget σ) := by
  rw [geometricTermOrdinaryEndpointCoefficient_eq, twist_twist]
  apply congrArg (fun c : K →* ℂˣ =>
    twist c ((Jacquet.action σ S Ls hSource.levi_le_normalizer).comp p))
  exact geometricNormalizedCompactCharacter_eq_epsilonEndpoints
    i ν I J dI dJ n (hU I) (hU J) (hM I) (hM J) hSource hTarget
      hPJ hPI hStandard hG hi hν hN hUJc hpI hpJ

/-- The actual normalized compact coefficient is the epsilon product twist
of the published geometric term's actual inducing representation. The map
preserves each original ordinary Jacquet class as a trivial-localization class. -/
def geometricNormalizedCompactActualCoefficientEquiv
    (σ : SmoothRep.{0,u,uV} ℂ MJ) :
    Representation.Equiv
      (geometricNormalizedCompactCoefficient i ν I J dI dJ n (hU I) (hU J) hPJ
        hSource hTarget σ.representation)
      (twist ε (geometricTermActualCoefficient i ν I J n hM hU hSource hTarget σ)) :=
  (equivOfRepresentationEq
    (geometricNormalizedCompactCoefficient_eq_epsilonOrdinaryEndpoints
      i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hStandard hG hi hν hN
        hUJc hpI hpJ σ.representation)).trans
    (twistEquiv ε (geometricTermActualCoefficientEquiv
      i ν I J n hM hU hSource hTarget σ).symm)

@[simp] theorem geometricNormalizedCompactActualCoefficientEquiv_mk
    (σ : SmoothRep.{0,u,uV} ℂ MJ) (v : σ) :
    geometricNormalizedCompactActualCoefficientEquiv
        i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hStandard hG hi hν hN
          hUJc hpI hpJ σ (Jacquet.mk σ.representation S v) =
      Jacquet.Localization.mk σ.representation S 1 v := by
  rfl

@[simp] theorem geometricNormalizedCompactActualCoefficientEquiv_symm_mk
    (σ : SmoothRep.{0,u,uV} ℂ MJ) (v : σ) :
    (geometricNormalizedCompactActualCoefficientEquiv
        i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hStandard hG hi hν hN
          hUJc hpI hpJ σ).symm (Jacquet.Localization.mk σ.representation S 1 v) =
      Jacquet.mk σ.representation S v := by
  rfl

/-- The complete coefficient identification is natural for the actual
inducing functor maps. Twisting by the two epsilons does not alter those maps. -/
theorem geometricNormalizedCompactActualCoefficientEquiv_natural
    {σ τ : SmoothRep.{0,u,uV} ℂ MJ} (a : σ ⟶ τ)
    (z : Jacquet.Coinvariants σ.representation S) :
    geometricNormalizedCompactActualCoefficientEquiv
      i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hStandard hG hi hν hN
        hUJc hpI hpJ τ
        (Jacquet.map S Ls hSource.levi_le_normalizer (SmoothRep.hom a) z) =
      ((geometricTermInducingFunctor
        (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J (n : A)
        hSource hTarget).map a).hom
        (geometricNormalizedCompactActualCoefficientEquiv
          i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hStandard hG hi hν hN
            hUJc hpI hpJ σ z) := by
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective σ.representation S z
  change geometricNormalizedCompactActualCoefficientEquiv
    i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hStandard hG hi hν hN
      hUJc hpI hpJ τ (Jacquet.mk τ.representation S (SmoothRep.hom a v)) = _
  rw [geometricNormalizedCompactActualCoefficientEquiv_mk,
    geometricNormalizedCompactActualCoefficientEquiv_mk,
    geometricTermInducingFunctor_map_mk]

end RationalPointFamily
end Langlands.Aubert.General
