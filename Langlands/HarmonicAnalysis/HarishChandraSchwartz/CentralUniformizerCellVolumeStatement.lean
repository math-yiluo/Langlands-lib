import Langlands.AlgebraicGeometry.PointTopology.RationalPointHaarProof
import Langlands.Analysis.Local.QuotientMeasure
import Langlands.GroupScheme.Rational.Characters
import Langlands.Representation.Plancherel.RenardUniformizerSection
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.MeasureTheory.Group.Measure

/-! # Double-coset volume on the central uniformizer quotient -/

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.HarishChandraSchwartz

open GroupScheme Plancherel QuotientIntegration Langlands.AlgebraicGeometry.PointTopology

/-- Each compact-open double coset embeds in the central uniformizer quotient
and has the same mass there for the counting-compatible measure. -/
def CentralUniformizerCellVolumeStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
      (A : CommGroupScheme (Spec (CommRingCat.of F))) (a : A.toGrp ⟶ G),
    IsSplitComponent a →
    haveI := hG.isAffineHom
    haveI := hG.smooth
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    haveI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    haveI : SecondCountableTopology (rationalPoints G) := rationalPoint_secondCountableTopology F G
    let C := RenardCartan.C0 A a
    ∀ (K : OpenSubgroup (rationalPoints G)), IsCompact (K : Set (rationalPoints G)) →
      ∀ g : rationalPoints G,
        let D := DoubleCoset.doubleCoset g K K
        Set.InjOn (leftQuotientMap C) D ∧
        ∀ [MeasurableSpace (rationalPoints G)] [BorelSpace (rationalPoints G)]
          [MeasurableSpace C] [BorelSpace C]
          [MeasurableSpace (LeftQuotient C)] [BorelSpace (LeftQuotient C)]
          (μG : Measure (rationalPoints G)) [μG.IsHaarMeasure]
          (μQ : Measure (LeftQuotient C)),
          IsCompatible C μG Measure.count μQ → μQ (leftQuotientMap C '' D) = μG D

end Langlands.HarishChandraSchwartz
