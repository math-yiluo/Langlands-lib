import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDiscreteSeriesOrbitFiniteness

/-! # Local discrete-series orbit finiteness

The fixed-field, fixed-group form of Waldspurger VIII.1.2 and its transfer to the
published standard rational Levi model. No analytic finiteness is proved here.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

/-- The fixed-field, fixed-group assertion of VIII.1.2, retaining every split
component, quotient Haar measure, and compact open level. The representation
carrier universe `uV` is independent of the field universe `u`. -/
def RationalLocalDiscreteSeriesOrbitFinitenessStatement
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] : Prop :=
  ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G)
    (hs : IsSplitComponent s),
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : NonarchimedeanGroup (rationalPoints G) := rationalPoints_nonarchimedeanGroup G
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range))
      [mu.IsHaarMeasure] (H : Subgroup (rationalPoints G)),
      IsOpen (H : Set (rationalPoints G)) → IsCompact (H : Set (rationalPoints G)) →
        (rationalDiscreteSeriesFixedOrbits.{u, uV} G s mu
          hs.isCentralSplitTorus.isCentral H).Finite

/-- All-field, all-connected-reductive-group closure of the local predicate. -/
def RationalLocalDiscreteSeriesOrbitFinitenessGlobalStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G → RationalLocalDiscreteSeriesOrbitFinitenessStatement.{u, uV} G

/-- The local closure is exactly the published VIII.1.2 assertion. -/
theorem rationalLocalDiscreteSeriesOrbitFinitenessGlobal_iff :
    RationalLocalDiscreteSeriesOrbitFinitenessGlobalStatement.{u, uV} ↔
      RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV} := Iff.rfl

/-- Specialize the global assertion to one connected reductive group. -/
theorem rationalLocalDiscreteSeriesOrbitFiniteness_of_global
    (hVIII : RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G) :
    RationalLocalDiscreteSeriesOrbitFinitenessStatement.{u, uV} G :=
  hVIII F G hG

section StandardLevi

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

local instance localLeviIsAffineHom (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J

local instance localLeviIsAffine (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) : IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom

local instance localLeviLocallyOfFiniteType (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) : LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (I : Finset (RationalPointFamily.SimpleRoot i ν))

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

set_option hygiene false in
local notation "𝐋" => Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)

/-- Local VIII.1.2 for the standard Levi scheme suffices for finiteness in the
published literal subgroup model `M_I(F)`. No finiteness premise on the ambient
`G` or on any other group is used. The proof uses the published rational-point
homeomorphism, norm-character comparison, and Haar-measure/orbit transfer. -/
theorem finite_discreteSeriesFixedOrbits_standardLevi_of_local
    (hVIII : RationalLocalDiscreteSeriesOrbitFinitenessStatement.{u, uV} 𝐋)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (a : T.toGrp ⟶ 𝐋)
    (ha : IsSplitComponent a)
    [(rationalLeviSplitCenter I a).Normal]
    [MeasurableSpace (𝐌 ⧸ rationalLeviSplitCenter I a)]
    [BorelSpace (𝐌 ⧸ rationalLeviSplitCenter I a)]
    (μM : Measure (𝐌 ⧸ rationalLeviSplitCenter I a)) [μM.IsHaarMeasure]
    (L : OpenSubgroup 𝐌) (hL : IsCompact (L : Set 𝐌)) :
    (discreteSeriesFixedOrbits (rationalLeviSplitCenter I a)
      (rationalLeviSplitCenter_le_center I a ha) μM
      (RationalPointFamily.leviRationalNormCharacters i ν I) L.toSubgroup :
        Set (DiscreteSeriesOrbitClass.{u, u, uV} (rationalLeviSplitCenter I a)
          (rationalLeviSplitCenter_le_center I a ha) μM
          (RationalPointFamily.leviRationalNormCharacters i ν I))).Finite := by
  have : NonarchimedeanGroup (rationalPoints 𝐋) := rationalPoints_nonarchimedeanGroup 𝐋
  let e := RationalPointFamily.leviRationalPointHomeomorph i ν I
  let B := (rationalPoints.map a).range
  have : B.Normal := B.normal_of_le_center ha.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints 𝐋 ⧸ B) := borel _
  have : BorelSpace (rationalPoints 𝐋 ⧸ B) := ⟨rfl⟩
  have hAB : B.map e.toMulEquiv.toMonoidHom = rationalLeviSplitCenter I a := rfl
  let φ := quotientContinuousMulEquiv e (rationalLeviSplitCenter I a) B hAB
  let μH : Measure (rationalPoints 𝐋 ⧸ B) := μM.map φ.symm
  have hμ : μH.map φ = μM := MeasurableEquiv.map_map_symm φ.toHomeomorph.toMeasurableEquiv
  have hLo : IsOpen ((L.toSubgroup.comap e.toMonoidHom : Subgroup (rationalPoints 𝐋)) :
      Set (rationalPoints 𝐋)) := L.isOpen.preimage e.continuous
  have hLc : IsCompact ((L.toSubgroup.comap e.toMonoidHom : Subgroup (rationalPoints 𝐋)) :
      Set (rationalPoints 𝐋)) := e.toHomeomorph.isCompact_preimage.mpr hL
  have hfin := hVIII T a ha μH (L.toSubgroup.comap e.toMonoidHom) hLo hLc
  exact finite_discreteSeriesFixedOrbits_of_pullback e
    (RationalPointFamily.leviRationalNormCharacters i ν I)
    (fun psi => (rationalNormCharacters 𝐋 psi).toMul)
    (fun χ m => RationalPointFamily.leviRationalNormCharacters_apply_points i ν I χ m)
    (rationalLeviSplitCenter I a) (rationalLeviSplitCenter_le_center I a ha) B
    ha.isCentralSplitTorus.isCentral.range_le_center hAB μM μH hμ L.toSubgroup hfin

end StandardLevi

end Langlands.HarishChandraSchwartz
