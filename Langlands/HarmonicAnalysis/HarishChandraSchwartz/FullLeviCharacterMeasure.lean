import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviScheme
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitCentralFiberAdapter
import Langlands.Representation.Plancherel.RationalUnitaryCharacterIso
import Langlands.Representation.Plancherel.StandardLeviCharacterMeasure
import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer

/-! # The actual full-Levi character measure for a supplied ambient split component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

section Rational

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  [Fintype (RationalPointFamily.SimpleRoot i ν)]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

set_option hygiene false in
local notation "𝐋" => Standard.leviScheme i ν (RationalPointFamily.rootSet i ν Finset.univ)
set_option hygiene false in
local notation "νL" => (fun ψ => (rationalNormCharacters 𝐋 ψ).toMul)
set_option hygiene false in
local notation "νG" => (fun ψ => (rationalNormCharacters G ψ).toMul)
set_option hygiene false in
local notation "νM" => RationalPointFamily.leviRationalNormCharacters i ν Finset.univ
set_option hygiene false in
local notation "e" => rationalFullLeviSchemeIso hG hi hν
set_option hygiene false in
local notation "eM" => RationalPointFamily.leviRationalPointHomeomorph i ν Finset.univ

local instance : IsAffineHom 𝐋.X.hom := leviScheme_isAffineHom i ν _
local instance : IsAffine 𝐋.X.left := isAffine_of_isAffineHom 𝐋.X.hom
local instance : LocallyOfFiniteType 𝐋.X.hom := leviScheme_locallyOfFiniteType i ν _
local instance : TopologicalSpace (rationalPoints 𝐋) := rationalPointTopology F 𝐋.X

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)

/-- The supplied ambient split component, factored through the actual
full-index standard Levi scheme, without choosing a new split component. -/
def rationalFullLeviSplitComponent : T.toGrp ⟶ 𝐋 := s ≫ (e).inv

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
include hs in
/-- The factor is still a split component, with the original source torus. -/
theorem isSplitComponent_rationalFullLeviSplitComponent :
    IsSplitComponent (rationalFullLeviSplitComponent hG hi hν s) :=
  hs.comp_iso (e).symm

/-- The actual unitary character groups used by the ambient and full-root
packet constructions, with their possibly different norm index types. -/
def rationalFullLeviCharacterEquiv :
    unitaryUnramifiedCharacters νG ≃ₜ* unitaryUnramifiedCharacters νM :=
  (rationalUnitaryCharacterIso (e).symm).trans
    (standardLeviUnitaryCharacterHomeomorph (i := i) (ν := ν) Finset.univ)

omit [LocallyOfFiniteType G.X.hom] in
/-- A transported character evaluates on the literal Levi by the original
ambient character on that same ambient group element. -/
theorem rationalFullLeviCharacterEquiv_apply
    (χ : unitaryUnramifiedCharacters νG)
    (m : standardLeviPoints i ν (RationalPointFamily.rootSet i ν Finset.univ)) :
    (rationalFullLeviCharacterEquiv hG hi hν χ).val m = χ.val (m : rationalPoints G) := by
  change χ.val (rationalPoints.map (e).hom ((eM).symm m)) = _
  rw [rationalFullLeviSchemeIso_hom]
  exact congrArg χ.val (congrArg Subtype.val ((eM).apply_symm_apply m))

set_option hygiene false in
local notation "sL" => rationalFullLeviSplitComponent hG hi hν s
set_option hygiene false in
local notation "hsL" => isSplitComponent_rationalFullLeviSplitComponent hG hi hν s hs
set_option hygiene false in
local notation "hindexG" => finiteIndex_splitValuationImage_of_isSplitComponent hG s hs
set_option hygiene false in
local notation "hindexL" => finiteIndex_splitValuationImage_of_isSplitComponent
  (isConnectedReductive_leviScheme_rootSet hG hi hν Finset.univ) sL hsL

variable [IsAffine T.X.left]

include hs in
/-- The exact I.1 character measure used by the full-root packet is the
pushforward of the ambient I.1 measure for the originally supplied split
component. Both finite-index inputs are proved from split-component structure. -/
theorem map_rationalFullLeviCharacterEquiv_Haar :
    Measure.map (rationalFullLeviCharacterEquiv hG hi hν)
      (rationalUnitaryUnramifiedCharacterHaar s hs.isCentralSplitTorus.isCentral hindexG) =
        standardLeviUnitaryUnramifiedCharacterHaar Finset.univ sL hsL hindexL := by
  have hm := map_rationalUnitaryUnramifiedCharacterHaar_of_iso s (e).symm
    hs.isCentralSplitTorus.isCentral (hsL).isCentralSplitTorus.isCentral hindexG hindexL
  change Measure.map
      ((standardLeviUnitaryCharacterHomeomorph (i := i) (ν := ν) Finset.univ) ∘
        rationalUnitaryCharacterIso (e).symm)
      (rationalUnitaryUnramifiedCharacterHaar s hs.isCentralSplitTorus.isCentral hindexG) =
    Measure.map (standardLeviUnitaryCharacterHomeomorph (i := i) (ν := ν) Finset.univ)
      (rationalUnitaryUnramifiedCharacterHaar sL (hsL).isCentralSplitTorus.isCentral hindexL)
  rw [← Measure.map_map
    (g := fun χ => standardLeviUnitaryCharacterHomeomorph (i := i) (ν := ν) Finset.univ χ)
    (f := fun χ => rationalUnitaryCharacterIso (e).symm χ)
    (standardLeviUnitaryCharacterHomeomorph (i := i) (ν := ν) Finset.univ).continuous.measurable
    (rationalUnitaryCharacterIso (e).symm).continuous.measurable, hm]
  rfl

end Rational

end Langlands.HarishChandraSchwartz
