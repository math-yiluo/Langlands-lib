import Langlands.Representation.Plancherel.DynamicRankOneGalleryFactors
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterCoordinates

/-! # The scalar on a same-chamber gallery step -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General.RepresentedParabolic DynamicCommonLeviComposition
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G) (ha : IsSplitComponent a)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

set_option hygiene false in
local notation "d" => galleryVertexData (χ := χ) hG ha
set_option hygiene false in
local notation "X" => unramifiedCharacters (normCharacters χ)
set_option hygiene false in
local notation "H" => parameterScheme χ
set_option hygiene false in
local notation "hH" => parameterScheme_isConnectedReductive χ hG
set_option hygiene false in
local notation "Lattice" => Additive (rationalDiscreteValuationImage H)

variable (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))

set_option hygiene false in
local notation "twisted" => fun z : X => σ.twist z.val.toMonoidHom
  (unramifiedCharacter_isOpen_ker (normCharacters χ) z)
set_option hygiene false in
local notation "Scalar" => IsGalleryCompositeScalar hG ha K hK

/-- Put the entire original valuation lattice in the translation block. -/
def constantFactorCoordinates : Lattice ≃ₗ[ℤ] (Fin 0 → ℤ) × (Fin (rationalImageRank H) → ℤ) :=
  (rationalReductiveValuationBasis H hH).equivFun.trans
    (LinearEquiv.uniqueProd (R := ℤ) (M₂ := Fin 0 → ℤ)).symm

set_option maxHeartbeats 1400000 in
/-- A same-chamber step contributes a constant scalar on a nonzero principal open. -/
theorem hasGenericRankOneGalleryFactorCoordinates_of_sameChamber
    {x y : GalleryVertex χ} (hChamber : SameDynamicChamber x.val y.val)
    (hσ : σ.IsIrreducible) (hA : σ.IsAdmissible) :
    HasGenericRankOneGalleryFactorCoordinates hG ha K hK σ x y := by
  classical
  have hr : radical x.val = radical y.val :=
    congrArg (fun U : SubgroupFunctor G => U.carrier (Over.mk (𝟙 _))) hChamber.2.1
  have hbar : oppositeRadical x.val = oppositeRadical y.val :=
    congrArg (fun U : SubgroupFunctor G => U.carrier (Over.mk (𝟙 _))) hChamber.2.2
  have hd : IsDistanceAdditive x.val y.val x.val :=
    ⟨inf_le_left.trans hr.le, inf_le_left.trans hbar.le⟩
  obtain ⟨c, _, hcomp⟩ := exists_galleryIntegralOperator_comp_smul.{u, uV} hG ha K hK x y x hd
  obtain ⟨p, hp, hReg⟩ := exists_generic_galleryRegular (χ := χ) hG ha ({x} : Finset (GalleryVertex χ))
    σ hσ hA
  refine ⟨p, 0, rationalImageRank H, constantFactorCoordinates (χ := χ) hG,
    fun _ => (c : ℂ), hp, Nat.zero_le 1, fun _ _ _ _ => rfl, ?_⟩
  intro z hz hPQ hQP
  have hx : x ∈ ({x} : Finset (GalleryVertex χ)) := Finset.mem_singleton_self _
  have hxx := hReg z hz x hx x hx
  have hc := hcomp (twisted z) hPQ hQP hxx
  have hself := galleryIntegralOperator_self hG ha K hK (twisted z) x hxx
  exact hc.trans (congrArg (fun f => (c : ℂ) • f) hself)

end Langlands.Plancherel.DynamicCommonLeviPresentations
