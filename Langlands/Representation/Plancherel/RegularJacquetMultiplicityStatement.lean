import Langlands.Representation.Plancherel.ParabolicGenericIrreducibilityStatement
import Langlands.Representation.Aubert.General.NormalizerRegularity

/-! # Multiplicity one for actual regular square-integrable parabolic induction -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe u uV

open Aubert.General

/-- The Jacquet multiplicity consequence of Waldspurger III.7.3, formulated
for the literal subgroup model and the positive Levi normalization. -/
def RegularSquareIntegrableJacquetMultiplicityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [T2Space (rationalPoints G)]
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      (M P U : GroupScheme (Spec (CommRingCat.of F))) [IsAffine M.X.left]
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) (n : U ⟶ P)
      (r : ParabolicRootPresentation p l a)
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n),
      let Ppt := (SubgroupFunctor.range p).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))
      let Mpt := parabolicLeviPointSubgroup p l
      let Upt := (SubgroupFunctor.range (n ≫ p)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))
      ∀ (h : IsSemidirectDecomposition Ppt Mpt Upt)
        (hU : IsClosed (Upt : Set (rationalPoints G)))
        (_hP : IsClosed (Ppt : Set (rationalPoints G)))
        (_hr : Continuous h.projection),
        let C := (parabolicSplitComponentPointHom r).range
        let hC := parabolicSplitComponentPointHom_range_le_center r
        letI : C.Normal := C.normal_of_le_center hC
        ∀ [MeasurableSpace (Mpt ⧸ C)] [BorelSpace (Mpt ⧸ C)]
          (qMeasure : Measure (Mpt ⧸ C)) [IsHaarMeasure qMeasure]
          (π : SmoothRep.{0, u, uV} ℂ Mpt),
          π.IsIrreducible →
          IsSquareIntegrableModCentralSubgroup C hC π.representation qMeasure →
          IsNormalizerRegular π →
          Module.rank ℂ (((jacquetFunctor h hU).obj
            ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj π)).representation.IntertwiningMap
              π.representation) ≤ 1

end Langlands.Plancherel
