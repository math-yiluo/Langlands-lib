import Langlands.Representation.Aubert.General.RationalGeometricNormalizedCompactNaturality

/-! # The actual normalized compact comparison as a natural isomorphism -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

universe u uV uW uX

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Induction MeasureTheory MeasureTheory.Measure
open QuotientIntegration HarmonicAnalysis
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
  (hUI : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hUJ : IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))
  (hSource : GeometricSourceDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  (hTarget : GeometricTargetDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))

local notation "Q" => parabolic i ν I
local notation "L" => levi i ν I
local notation "H" => Subgroup.subgroupOf
  (geometricTargetIntersection Q (parabolic i ν J) (n : RationalPoint k G.X)) Q
local notation "K" => Subgroup.subgroupOf
  (geometricTargetIntersection L (parabolic i ν J) (n : RationalPoint k G.X)) L
local notation "S" => Subgroup.subgroupOf
  (geometricSourceIntersection (unipotent i ν I) (levi i ν J)
    (n : RationalPoint k G.X)) (levi i ν J)
local notation "Ls" => Subgroup.subgroupOf
  (geometricSourceIntersection L (levi i ν J)
    (n : RationalPoint k G.X)) (levi i ν J)
local notation "f" => geometricCoefficientProjection
  Q (parabolic i ν J) (levi i ν J) (unipotent i ν J) dJ (n : RationalPoint k G.X)
local notation "p" => geometricCoefficientLeviMap
  L (parabolic i ν J) (levi i ν J) (unipotent i ν J)
  (n : RationalPoint k G.X) hTarget
local notation "s" => Subgroup.inclusion dI.levi_le
local notation "P" => geometricSplitIntermediate i ν I J dI n
local notation "N" => geometricCompactKernel i ν I J dI n
local notation "D" => geometricCompactKernelIntersection i ν I J dI n
local notation "χ" => HaarModulus.closedHalfCharacter
  (unipotent i ν J) hUJ (levi i ν J) dJ.levi_le_normalizer
local notation "κ" => HaarModulus.closedInverseHalfCharacter
  (unipotent i ν I) hUI L dI.levi_le_normalizer
local notation "η" => geometricNormalizedCompactCharacter i ν I J dI dJ n hUI hUJ hPJ hTarget
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- The original normalized compact quotient map preserves identity maps. -/
@[simp] theorem geometricNormalizedCompactSourceMap_id
    (σ : Representation ℂ (levi i ν J) V) :
    geometricNormalizedCompactSourceMap i ν I J dI dJ n hUI hUJ
        (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id
        (geometricNormalizedCompactSource i ν I J dI dJ n hUI hUJ σ) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  refine Representation.Coinvariants.induction_on z ?_
  intro F
  change Representation.Coinvariants.mk _
    (compactInducedMap H (restrictAlongMap f
      (twistIntertwining χ (Representation.IntertwiningMap.id σ))) F) =
    Representation.Coinvariants.mk _ F
  apply congrArg (Representation.Coinvariants.mk _)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext q
  rfl

/-- The original normalized compact quotient map preserves composition. -/
@[simp] theorem geometricNormalizedCompactSourceMap_comp
    {σ : Representation ℂ (levi i ν J) V} {τ : Representation ℂ (levi i ν J) W}
    {υ : Representation ℂ (levi i ν J) X}
    (a : σ.IntertwiningMap τ) (b : τ.IntertwiningMap υ) :
    geometricNormalizedCompactSourceMap i ν I J dI dJ n hUI hUJ (b.comp a) =
      (geometricNormalizedCompactSourceMap i ν I J dI dJ n hUI hUJ b).comp
        (geometricNormalizedCompactSourceMap i ν I J dI dJ n hUI hUJ a) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  refine Representation.Coinvariants.induction_on z ?_
  intro F
  rfl

/-- The original ordinary-quotient coefficient map preserves identity maps. -/
@[simp] theorem geometricNormalizedCompactCoefficientMap_id
    (σ : Representation ℂ (levi i ν J) V) :
    geometricNormalizedCompactCoefficientMap i ν I J dI dJ n hUI hUJ hPJ hSource hTarget
        (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id
        (geometricNormalizedCompactCoefficient i ν I J dI dJ n hUI hUJ hPJ
          hSource hTarget σ) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  refine Representation.Coinvariants.induction_on z ?_
  intro v
  rfl

/-- The original ordinary-quotient coefficient map preserves composition. -/
@[simp] theorem geometricNormalizedCompactCoefficientMap_comp
    {σ : Representation ℂ (levi i ν J) V} {τ : Representation ℂ (levi i ν J) W}
    {υ : Representation ℂ (levi i ν J) X}
    (a : σ.IntertwiningMap τ) (b : τ.IntertwiningMap υ) :
    geometricNormalizedCompactCoefficientMap i ν I J dI dJ n hUI hUJ hPJ hSource hTarget
        (b.comp a) =
      (geometricNormalizedCompactCoefficientMap i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget b).comp
        (geometricNormalizedCompactCoefficientMap i ν I J dI dJ n hUI hUJ hPJ
          hSource hTarget a) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  refine Representation.Coinvariants.induction_on z ?_
  intro v
  rfl

/-- The actual normalized compact target map preserves identity maps. -/
@[simp] theorem geometricNormalizedCompactTargetMap_id
    (σ : Representation ℂ (levi i ν J) V) :
    geometricNormalizedCompactTargetMap i ν I J dI dJ n hUI hUJ hPJ hSource hTarget
        (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id
        (geometricNormalizedCompactTarget i ν I J dI dJ n hUI hUJ hPJ
          hSource hTarget σ) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext l
  exact congrArg (fun a => a (eval K
    (geometricNormalizedCompactCoefficient i ν I J dI dJ n hUI hUJ hPJ
      hSource hTarget σ) F.val l))
    (geometricNormalizedCompactCoefficientMap_id
      i ν I J dI dJ n hUI hUJ hPJ hSource hTarget σ)

/-- The actual normalized compact target map preserves composition. -/
@[simp] theorem geometricNormalizedCompactTargetMap_comp
    {σ : Representation ℂ (levi i ν J) V} {τ : Representation ℂ (levi i ν J) W}
    {υ : Representation ℂ (levi i ν J) X}
    (a : σ.IntertwiningMap τ) (b : τ.IntertwiningMap υ) :
    geometricNormalizedCompactTargetMap i ν I J dI dJ n hUI hUJ hPJ hSource hTarget
        (b.comp a) =
      (geometricNormalizedCompactTargetMap i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget b).comp
        (geometricNormalizedCompactTargetMap i ν I J dI dJ n hUI hUJ hPJ
          hSource hTarget a) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext l
  exact congrArg (fun c => c (eval K
    (geometricNormalizedCompactCoefficient i ν I J dI dJ n hUI hUJ hPJ
      hSource hTarget σ) F.val l))
    (geometricNormalizedCompactCoefficientMap_comp
      i ν I J dI dJ n hUI hUJ hPJ hSource hTarget a b)

variable [T2Space (RationalPoint k G.X)]
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hMI : IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (hMJ : IsClosed (levi i ν J : Set (RationalPoint k G.X)))
  (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  (hprojI : Continuous dI.projection) (hprojJ : Continuous dJ.projection)

/-- The actual original compact orbit quotient with both endpoint halves,
as a functor on smooth representations. -/
def geometricNormalizedCompactSourceFunctor :
    SmoothRep.{0,u,uV} ℂ (levi i ν J) ⥤ SmoothRep.{0,u,max u uV} ℂ L where
  obj A := SmoothRep.of
    (geometricNormalizedCompactSource i ν I J dI dJ n hUI hUJ A.representation)
    (isSmooth_geometricNormalizedCompactSource i ν I J dI dJ n hUI hUJ hPJ
      hSource hTarget hPI hMJ hUc hStandard hG hi hν hN hMI hprojI hprojJ
      A.representation A.isSmooth)
  map a := SmoothRep.ofHom
    (geometricNormalizedCompactSourceMap i ν I J dI dJ n hUI hUJ (SmoothRep.hom a))
  map_id A := congrArg SmoothRep.ofHom
    (geometricNormalizedCompactSourceMap_id i ν I J dI dJ n hUI hUJ A.representation)
  map_comp a b := congrArg SmoothRep.ofHom
    (geometricNormalizedCompactSourceMap_comp i ν I J dI dJ n hUI hUJ
      (SmoothRep.hom a) (SmoothRep.hom b))

/-- Compact induction of the original ordinary Jacquet quotient with its exact
full-intersection coefficient character, as a smooth functor. -/
def geometricNormalizedCompactTargetFunctor :
    SmoothRep.{0,u,uV} ℂ (levi i ν J) ⥤ SmoothRep.{0,u,max u uV} ℂ L where
  obj A := SmoothRep.of
    (geometricNormalizedCompactTarget i ν I J dI dJ n hUI hUJ hPJ
      hSource hTarget A.representation) (compactInduced_smooth _ _)
  map a := SmoothRep.ofHom
    (geometricNormalizedCompactTargetMap i ν I J dI dJ n hUI hUJ hPJ
      hSource hTarget (SmoothRep.hom a))
  map_id A := congrArg SmoothRep.ofHom
    (geometricNormalizedCompactTargetMap_id i ν I J dI dJ n hUI hUJ hPJ hSource hTarget
      A.representation)
  map_comp a b := congrArg SmoothRep.ofHom
    (geometricNormalizedCompactTargetMap_comp i ν I J dI dJ n hUI hUJ hPJ
      hSource hTarget (SmoothRep.hom a) (SmoothRep.hom b))

/-- The actual normalized compact comparison, natural in every smooth input. -/
def geometricNormalizedCompactNatIso :
    geometricNormalizedCompactSourceFunctor i ν I J dI dJ n hUI hUJ hPJ hSource hTarget
        hPI hMI hMJ hUc hStandard hG hi hν hN hprojI hprojJ ≅
      geometricNormalizedCompactTargetFunctor i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget :=
  NatIso.ofComponents
    (fun A => geometricNormalizedCompactSmoothIso i ν I J dI dJ n hUI hUJ hPJ
      hSource hTarget hPI hMJ hUc hStandard hG hi hν hN hMI hprojI hprojJ A)
    (by
      intro A B a
      ext z
      exact geometricNormalizedCompactEquiv_natural
        i ν I J dI dJ n hUI hUJ hPJ hSource hTarget hPI hMI hMJ hUc hStandard hG hi hν hN
        hprojI hprojJ A.isSmooth B.isSmooth (SmoothRep.hom a) z)

end Langlands.Aubert.General.RationalPointFamily
