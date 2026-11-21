import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardInvariance
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardGlobalForm

/-! # Waldspurger's actual integral form on invariant families -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 900000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalForm

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

variable (hG : IsConnectedReductive G)
  {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ t, IsAffine (T t).X.left]
  (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
  (ha : ∀ t, IsSplitComponent (a t))
  [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
  [∀ t, (rationalPoints.map (a t)).range.Normal]
  [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  (mu : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
  [∀ t, (mu t).IsHaarMeasure] [∀ t, (mu t).IsInvInvariant]
  (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
  (rs : ∀ t : SemistandardSpectralIndex i, CocharacterPresentation hG t)
  (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
  (Q : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
    OrbitPacketData (rs theta.1)
      (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1)
        (mu theta.1) theta.2))
  (K0 : OpenSubgroup (rationalPoints G)) (hK0 : IsCompact (K0 : Set (rationalPoints G)))
  (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)

set_option hygiene false in
set_option quotPrecheck false in
local notation "Invariant" => rationalSemistandardThetaInvariantSections C
set_option hygiene false in
set_option quotPrecheck false in
local notation "B" => rawGlobalForm hG a ha mu d rs hindex Q K0 hK0

/-- Restrict the actual sesquilinear integral to the invariant subspace. -/
def invariantGlobalForm : Invariant →ₗ⋆[ℂ] Invariant →ₗ[ℂ] ℂ where
  toFun f := (B f.val).comp (Invariant).subtype
  map_add' f g := LinearMap.ext fun v =>
    congrArg (fun L => L v.val) ((B).map_add f.val g.val)
  map_smul' c f := LinearMap.ext fun v =>
    congrArg (fun L => L v.val) ((B).map_smulₛₗ c f.val)

@[simp] theorem invariantGlobalForm_apply (f g : Invariant) :
    invariantGlobalForm hG a ha mu d rs hindex Q K0 hK0 C f g = B f.val g.val := rfl

/-- The restriction retains invariance under the actual product action. -/
theorem invariantGlobalForm_action (x : rationalPoints G × rationalPoints G) (f g : Invariant) :
    invariantGlobalForm hG a ha mu d rs hindex Q K0 hK0 C
        (rationalSemistandardThetaInvariantRepresentation C x f)
        (rationalSemistandardThetaInvariantRepresentation C x g) =
      invariantGlobalForm hG a ha mu d rs hindex Q K0 hK0 C f g :=
  rawGlobalForm_action hG a ha mu d rs hindex Q K0 hK0 x f.val g.val

/-- The positive Hermitian form uses the same integral, under the full-family
positivity target and its exact density and geometric inputs. -/
def invariantGlobalPositiveForm
    (h : PositiveFormStatement hG a ha mu d rs hindex Q K0 hK0)
    (hfin : SemistandardSpectralFiberFinitenessStatement.{u}) (hi : IsMaximalSplitTorus i)
    (hn : DensityNonnegative hG a ha mu rs Q) (hdense : DensityPositiveDense hG a ha mu rs Q) :
    @InvariantPositiveForm (rationalPoints G × rationalPoints G) _ Invariant _ _
      (rationalSemistandardThetaInvariantRepresentation C) :=
  (invariantPositiveForm hG a ha mu d rs hindex Q K0 hK0 h hfin hi hn hdense).comap
    (rationalSemistandardThetaInvariantIntertwining C) Subtype.val_injective

@[simp] theorem invariantGlobalPositiveForm_inner
    (h : PositiveFormStatement hG a ha mu d rs hindex Q K0 hK0)
    (hfin : SemistandardSpectralFiberFinitenessStatement.{u}) (hi : IsMaximalSplitTorus i)
    (hn : DensityNonnegative hG a ha mu rs Q) (hdense : DensityPositiveDense hG a ha mu rs Q)
    (f g : Invariant) :
    (invariantGlobalPositiveForm hG a ha mu d rs hindex Q K0 hK0 C h hfin hi hn hdense).inner f g =
      invariantGlobalForm hG a ha mu d rs hindex Q K0 hK0 C f g := rfl

end Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalForm
