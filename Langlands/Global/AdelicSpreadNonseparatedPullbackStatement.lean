import Langlands.Global.AdelicSpreadModelPullbackStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.DoubledPointLine

/-! # Adelic fibre products over a nonseparated base: the doubled-origin line -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The affine line with doubled origin over `R`, as a scheme over `Spec R`: the gluing
`DoubledPointLine.glued R 1` of the lines `Spec R[t]` and `Spec R[s]` along `D(t)` and
`D(s - 1)` by `t = s - 1`. -/
def doubledOriginLine (R : Type u) [CommRing R] : Over (Spec (CommRingCat.of R)) :=
  Over.mk (DoubledPointLine.toBase R 1)

/-- The two affine-line charts of `doubledOriginLine R` as morphisms over `Spec R`:
`true` is the chart with coordinate `t`, `false` the chart with coordinate `s`. -/
def doubledOriginChart (R : Type u) [CommRing R] (b : Bool) :
    ringTest R (Polynomial R) ⟶ doubledOriginLine R :=
  Over.homMk (DoubledPointLine.ι R 1 ⟨b⟩) (DoubledPointLine.ι_toBase R 1 ⟨b⟩)

/-- Function fields with perfect constants: the doubled-origin line over the `S`-integers is
of finite type, and for every limit pullback cone of its two charts, the comparison of the
adelic points of the generic-fibre cone with the compatible pairs of adelic points of the
two lines is not a homeomorphism for the topologies from these models. -/
def CurvePlaceSpreadNonseparatedPullbackStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)),
    LocallyOfFiniteType (doubledOriginLine (curvePlaceSIntegers k F S)).hom ∧
    QuasiCompact (doubledOriginLine (curvePlaceSIntegers k F S)).hom ∧
    ∀ (c : PullbackCone (doubledOriginChart (curvePlaceSIntegers k F S) true)
        (doubledOriginChart (curvePlaceSIntegers k F S) false)), IsLimit c →
      let G := Over.pullback
        (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))
      let L := ringTest (curvePlaceSIntegers k F S) (Polynomial (curvePlaceSIntegers k F S))
      letI : TopologicalSpace (CurvePlaceAdelePoints k F (G.obj L)) :=
        curvePlaceSpreadAdelePointTopology k F S L (G.obj L) (Iso.refl _)
      ¬ @IsHomeomorph
        (CurvePlaceAdelePoints k F (G.obj c.pt))
        {q : CurvePlaceAdelePoints k F (G.obj L) × CurvePlaceAdelePoints k F (G.obj L) //
          q.1 ≫ G.map (doubledOriginChart (curvePlaceSIntegers k F S) true) =
            q.2 ≫ G.map (doubledOriginChart (curvePlaceSIntegers k F S) false)}
        (curvePlaceSpreadAdelePointTopology k F S c.pt (G.obj c.pt) (Iso.refl _))
        inferInstance
        (affineSchemePullbackPointComparison F (CurvePlaceAdeleRing k F) (c.map G))

/-- Number fields: the doubled-origin line over the `S`-integers is of finite type, and for
every limit pullback cone of its two charts, the comparison of the adelic points of the
generic-fibre cone with the compatible pairs of adelic points of the two lines is not a
homeomorphism for the topologies from these models. -/
def NumberFieldSpreadNonseparatedPullbackStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K)),
    LocallyOfFiniteType (doubledOriginLine ((S : Set (FinitePlace K)).integer K)).hom ∧
    QuasiCompact (doubledOriginLine ((S : Set (FinitePlace K)).integer K)).hom ∧
    ∀ (c : PullbackCone (doubledOriginChart ((S : Set (FinitePlace K)).integer K) true)
        (doubledOriginChart ((S : Set (FinitePlace K)).integer K) false)), IsLimit c →
      let G := Over.pullback
        (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype))
      let L := ringTest ((S : Set (FinitePlace K)).integer K)
        (Polynomial ((S : Set (FinitePlace K)).integer K))
      letI : TopologicalSpace (NumberFieldAdelePoints K (G.obj L)) :=
        numberFieldSpreadAdelePointTopology K S L (G.obj L) (Iso.refl _)
      ¬ @IsHomeomorph
        (NumberFieldAdelePoints K (G.obj c.pt))
        {q : NumberFieldAdelePoints K (G.obj L) × NumberFieldAdelePoints K (G.obj L) //
          q.1 ≫ G.map (doubledOriginChart ((S : Set (FinitePlace K)).integer K) true) =
            q.2 ≫ G.map (doubledOriginChart ((S : Set (FinitePlace K)).integer K) false)}
        (numberFieldSpreadAdelePointTopology K S c.pt (G.obj c.pt) (Iso.refl _))
        inferInstance
        (affineSchemePullbackPointComparison K (Adeles K) (c.map G))

/-- Both arithmetic forms of the doubled-origin counterexample to adelic fibre-product
compatibility over a nonseparated base. -/
def AdelicSpreadNonseparatedPullbackStatement : Prop :=
  CurvePlaceSpreadNonseparatedPullbackStatement.{u} ∧
    NumberFieldSpreadNonseparatedPullbackStatement.{u}

end Langlands.Global
