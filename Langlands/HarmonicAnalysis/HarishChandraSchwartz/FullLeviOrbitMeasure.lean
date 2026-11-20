import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviCharacterMeasure
import Langlands.Representation.Plancherel.DiscreteSeriesOrbitTransport

/-! # Actual orbit measures at the full standard Levi -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

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
local notation "𝐌" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν Finset.univ)
set_option hygiene false in
local notation "νG" => (fun ψ => (rationalNormCharacters G ψ).toMul)
set_option hygiene false in
local notation "νM" => RationalPointFamily.leviRationalNormCharacters i ν Finset.univ

local instance : NonarchimedeanGroup (rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G
local instance : IsAffineHom
    (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν Finset.univ)).X.hom :=
  leviScheme_isAffineHom i ν _
local instance : IsAffine
    (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν Finset.univ)).X.left :=
  isAffine_of_isAffineHom
    (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν Finset.univ)).X.hom
local instance : TopologicalSpace (rationalPoints
    (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν Finset.univ))) :=
  rationalPointTopology F _

/-- The full literal standard Levi as the ambient rational-point group. -/
def rationalFullLeviLiteralPointEquiv : 𝐌 ≃ₜ* rationalPoints G :=
  (RationalPointFamily.leviRationalPointHomeomorph i ν Finset.univ).symm.trans
    (rationalFullLeviPointHomeomorph hG hi hν)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The forward function of the full literal Levi equivalence is inclusion. -/
theorem rationalFullLeviLiteralPointEquiv_apply (m : 𝐌) :
    rationalFullLeviLiteralPointEquiv hG hi hν m = (m : rationalPoints G) := by
  change rationalPoints.map (rationalFullLeviSchemeIso hG hi hν).hom
    ((RationalPointFamily.leviRationalPointHomeomorph i ν Finset.univ).symm m) = _
  rw [rationalFullLeviSchemeIso_hom]
  exact congrArg Subtype.val
    ((RationalPointFamily.leviRationalPointHomeomorph i ν Finset.univ).apply_symm_apply m)

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)

set_option hygiene false in
local notation "sL" => rationalFullLeviSplitComponent hG hi hν s
set_option hygiene false in
local notation "hsL" => isSplitComponent_rationalFullLeviSplitComponent hG hi hν s hs
set_option hygiene false in
local notation "A" => (rationalPoints.map s).range
set_option hygiene false in
local notation "hA" => hs.isCentralSplitTorus.isCentral.range_le_center
set_option hygiene false in
local notation "B" => rationalLeviSplitCenter Finset.univ sL
set_option hygiene false in
local notation "hB" => rationalLeviSplitCenter_le_center Finset.univ sL hsL
set_option hygiene false in
local notation "eG" => rationalFullLeviLiteralPointEquiv hG hi hν
set_option hygiene false in
local notation "eX" => rationalFullLeviCharacterEquiv hG hi hν
set_option hygiene false in
local notation "eM" => RationalPointFamily.leviRationalPointHomeomorph i ν Finset.univ
set_option hygiene false in
local notation "e" => rationalFullLeviSchemeIso hG hi hν

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [IsAffine T.X.left] in
/-- The factored split component has exactly the originally supplied
ambient point-image after the literal full-Levi identification. -/
theorem map_rationalFullLeviSplitCenter :
    (B).map (eG).toMonoidHom = A := by
  unfold rationalLeviSplitCenter
  rw [Subgroup.map_map, MonoidHom.map_range]
  apply congrArg MonoidHom.range
  apply MonoidHom.ext
  intro t
  change eG (eM (rationalPoints.map sL t)) = rationalPoints.map s t
  rw [rationalFullLeviLiteralPointEquiv_apply,
    RationalPointFamily.leviRationalPointHomeomorph_apply_coe,
    ← rationalFullLeviSchemeIso_hom hG hi hν]
  change (t ≫ (s ≫ (e).inv).hom.hom) ≫ (e).hom.hom.hom = t ≫ s.hom.hom
  simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Category.comp_id]

variable [(A).Normal] [(B).Normal] [(rationalPoints.map sL).range.Normal]
  [MeasurableSpace (rationalPoints G ⧸ A)] [BorelSpace (rationalPoints G ⧸ A)]
  [MeasurableSpace (𝐌 ⧸ B)] [BorelSpace (𝐌 ⧸ B)]
  (mu : Measure (rationalPoints G ⧸ A)) [mu.IsHaarMeasure]

/-- The literal quotient Haar measure corresponding to the arbitrary
ambient quotient Haar measure, via the actual full-Levi quotient map. -/
def rationalFullLeviQuotientHaar : Measure (𝐌 ⧸ B) :=
  Measure.map (quotientContinuousMulEquiv eG A B
    (map_rationalFullLeviSplitCenter hG hi hν s)).symm mu

instance rationalFullLeviQuotientHaar_isHaar :
    (rationalFullLeviQuotientHaar hG hi hν s mu).IsHaarMeasure :=
  (quotientContinuousMulEquiv eG A B
    (map_rationalFullLeviSplitCenter hG hi hν s)).symm.isHaarMeasure_map mu

omit [(rationalPoints.map sL).range.Normal] [mu.IsHaarMeasure]
  [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [IsAffine T.X.left] in
/-- The quotient measure is transported without rescaling. -/
theorem map_rationalFullLeviQuotientHaar :
    Measure.map (quotientContinuousMulEquiv eG A B
      (map_rationalFullLeviSplitCenter hG hi hν s))
      (rationalFullLeviQuotientHaar hG hi hν s mu) = mu :=
  MeasurableEquiv.map_map_symm
    (quotientContinuousMulEquiv eG A B
      (map_rationalFullLeviSplitCenter hG hi hν s)).toHomeomorph.toMeasurableEquiv

set_option hygiene false in
local notation "muM" => rationalFullLeviQuotientHaar hG hi hν s mu

/-- The same actual discrete-series class read on the full literal Levi. -/
def rationalFullLeviDiscreteSeriesClass (ω : DiscreteSeriesClass.{u, uV} A hA mu) :
    DiscreteSeriesClass.{u, uV} B hB muM :=
  DiscreteSeriesClass.pullback eG A hA B hB
    (map_rationalFullLeviSplitCenter hG hi hν s) mu muM
    (map_rationalFullLeviQuotientHaar hG hi hν s mu) ω

variable (ω : DiscreteSeriesClass.{u, uV} A hA mu)

set_option hygiene false in
local notation "ωM" => rationalFullLeviDiscreteSeriesClass hG hi hν s hs mu ω

/-- The actual ambient and full-root literal twist orbits, with their
stabilizer-quotient topologies and the same carrier universe. -/
def rationalFullLeviOrbitHomeomorph :
    discreteSeriesOrbit A hA mu νG ω ≃ₜ discreteSeriesOrbit B hB muM νM ωM :=
  discreteSeriesOrbitCharacterEquiv eG νG νM eX
    (fun χ m => by
      rw [rationalFullLeviCharacterEquiv_apply, rationalFullLeviLiteralPointEquiv_apply])
    A hA B hB (map_rationalFullLeviSplitCenter hG hi hν s) mu muM
    (map_rationalFullLeviQuotientHaar hG hi hν s mu) ω

set_option hygiene false in
local notation "hindexG" => finiteIndex_splitValuationImage_of_isSplitComponent hG s hs
set_option hygiene false in
local notation "hindexL" => finiteIndex_splitValuationImage_of_isSplitComponent
  (isConnectedReductive_leviScheme_rootSet hG hi hν Finset.univ) sL hsL

/-- The exact ambient I.1/VI.3 orbit measure is the full-root packet's
standard Levi orbit measure after transport. No probability convention is
introduced and neither finite-fiber factor is omitted. -/
theorem map_rationalFullLeviOrbitHomeomorph_measure :
    Measure.map (rationalFullLeviOrbitHomeomorph hG hi hν s hs mu ω)
      (rationalNormalizedDiscreteSeriesOrbitMeasure s hs.isCentralSplitTorus.isCentral mu
        hindexG ω) =
        standardLeviNormalizedDiscreteSeriesOrbitMeasure Finset.univ sL hsL hindexL muM ωM := by
  let := finite_rationalDiscreteSeriesStabilizer s hs.isCentralSplitTorus.isCentral mu hindexG ω
  let := finite_standardLeviDiscreteSeriesStabilizer Finset.univ sL hsL hindexL muM ωM
  let : Finite (discreteSeriesStabilizer B hB muM νM
      (DiscreteSeriesClass.pullback eG A hA B hB
        (map_rationalFullLeviSplitCenter hG hi hν s) mu muM
        (map_rationalFullLeviQuotientHaar hG hi hν s mu) ω)) :=
    finite_standardLeviDiscreteSeriesStabilizer Finset.univ sL hsL hindexL muM ωM
  rw [standardLeviNormalizedDiscreteSeriesOrbitMeasure_eq]
  change Measure.map
      (discreteSeriesOrbitCharacterEquiv eG νG νM eX _
        A hA B hB (map_rationalFullLeviSplitCenter hG hi hν s) mu muM
        (map_rationalFullLeviQuotientHaar hG hi hν s mu) ω)
      (discreteSeriesOrbitMeasure νG A hA mu ω
        (rationalUnitaryUnramifiedCharacterHaar s hs.isCentralSplitTorus.isCentral hindexG)) = _
  rw [map_discreteSeriesOrbitMeasure_characterEquiv, map_rationalFullLeviCharacterEquiv_Haar]
  · rfl
  · exact hs

end Langlands.HarishChandraSchwartz
