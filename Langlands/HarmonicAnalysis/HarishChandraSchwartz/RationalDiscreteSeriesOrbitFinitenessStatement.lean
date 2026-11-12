import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteSeriesOrbitFiniteness
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # Waldspurger's Theorem VIII.1.2 on actual rational points (statement)

`RationalDiscreteSeriesOrbitFinitenessStatement`: for every connected reductive group `G` over a
nonarchimedean local field `F` and every compact open subgroup `H` of `G(F)`, the set `Θ^H_G`
of unitary unramified twist orbits of discrete-series classes of `G(F)` (modulo the split
centre `A_G(F)`) having a nonzero `H`-fixed vector is finite.

`isConnectedReductive_centralizerScheme`: the actual Levi subgroups `Z_G(χ)` of the dynamic
parabolic subgroups `P_G(χ)` are connected reductive group schemes over `F`, so the statement
applies to them as well.
-/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.HarishChandraSchwartz

universe u uV

/-- **Waldspurger, Théorème VIII.1.2** (printed p. 321) on actual rational points. Let `F` be a
nonarchimedean local field, `G` a connected reductive group scheme over `F` with its canonical
rational-point topology, and `s : T → G` a split component, whose image `A_G(F)` is a closed
central subgroup of `G(F)`. For every Haar measure `mu` on `G(F)/A_G(F)` (with its Borel
structure) and every compact open subgroup `H` of `G(F)`, the set
`rationalDiscreteSeriesFixedOrbits G s mu _ H` (Waldspurger's `Θ^H_G`: the orbits under the
unitary unramified characters of the discrete-series classes of `G(F)` modulo `A_G(F)` that have a
nonzero `H`-fixed vector) is finite. -/
def RationalDiscreteSeriesOrbitFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G)
      (hs : IsSplitComponent s),
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      letI : NonarchimedeanGroup (rationalPoints G) := rationalPoints_nonarchimedeanGroup G
      letI := (rationalPoints.map s).range.normal_of_le_center
        hs.isCentralSplitTorus.isCentral.range_le_center
      letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
      ∀ (mu : MeasureTheory.Measure (rationalPoints G ⧸ (rationalPoints.map s).range))
        [MeasureTheory.Measure.IsHaarMeasure mu] (H : Subgroup (rationalPoints G)),
        IsOpen (H : Set (rationalPoints G)) → IsCompact (H : Set (rationalPoints G)) →
          (rationalDiscreteSeriesFixedOrbits.{u, uV} G s mu hs.isCentralSplitTorus.isCentral
            H).Finite

/-- The actual Levi subgroup `Z_G(χ)` of the dynamic parabolic `P_G(χ)` of a connected reductive
group `G` over a field is a connected reductive group scheme, so
`RationalDiscreteSeriesOrbitFinitenessStatement` applies to it (Waldspurger uses VIII.1.2 for the
Levi subgroups of `G` in VIII.1.3). This is the Library's `dynamicCentralizerReductive` applied to
the closed representative `Dynamic.Affine.centralizerHom χ`. -/
theorem isConnectedReductive_centralizerScheme {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    IsConnectedReductive (Dynamic.Affine.centralizerScheme χ) :=
  dynamicCentralizerReductive k G hG χ _ (Dynamic.Affine.centralizerHom χ)
    (Dynamic.Affine.isClosedSubgroup_centralizerHom χ)
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)

end Langlands.HarishChandraSchwartz
