import Langlands.Representation.Plancherel.ParabolicPointIntertwiningRegion
import Langlands.Representation.Plancherel.CompactIntertwiningFamilies
import Langlands.Representation.Plancherel.CentralSubgroupCoefficients

/-! # A conditional generic irreducibility prerequisite for scalar continuation -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe u uV

section SplitCenter

variable {F : Type u} [Field F] [TopologicalSpace F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance parabolicGenericIrreducibilityPointTopology : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance parabolicGenericIrreducibilityStatementTopologicalSpace : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X

/-- The actual image of the split component is central in the literal Levi. -/
theorem parabolicSplitComponentPointHom_range_le_center :
    (parabolicSplitComponentPointHom r).range ≤
      Subgroup.center (parabolicLeviPointSubgroup p l) := by
  rintro _ ⟨x, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro m
  obtain ⟨y, rfl⟩ := (parabolicLeviPointHomeomorph r).surjective m
  change (parabolicLeviPointHomeomorph r) y *
      (parabolicLeviPointHomeomorph r) (rationalPoints.map a x) =
    (parabolicLeviPointHomeomorph r) (rationalPoints.map a x) *
      (parabolicLeviPointHomeomorph r) y
  simpa only [map_mul] using
    congrArg (parabolicLeviPointHomeomorph r)
      (Subgroup.mem_center_iff.mp
        (r.isCompatible.splitComponent.1.isCentral.map_mem_center x) y)

end SplitCenter

open Aubert.General

/-- The character-space open-locus consequence used at the start of
Waldspurger IV.3 for square-integrable inducing representations. This is a
Prop target, not a proof or the full regularity assertion of IV.2.2. -/
def ConditionalParabolicGenericIrreducibilityStatement : Prop :=
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
          ∃ D : Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r)),
            IsOpen D ∧ D.Nonempty ∧
            ∀ χ ∈ D,
              (UnramifiedLeviInduction h hU
                (parabolicLeviRationalNormCharacters r) χ π).IsIrreducible

end Langlands.Plancherel
