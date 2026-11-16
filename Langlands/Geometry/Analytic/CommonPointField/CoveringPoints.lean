import Langlands.Geometry.Analytic.CommonPointField.Statement
import Langlands.Geometry.Analytic.EtaleGeometricPointStatement
import Langlands.Geometry.Analytic.EtaleCoveringPoints.Statement

/-! # Ordinary covering points from field-valued site points -/

noncomputable section

universe u v uL

open CategoryTheory

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The joint-surjectivity axiom at geometric points detects ordinary covering
points once every analytic space has a common point field. -/
theorem coveringPoints_of_commonPointFields
    (hfield : CommonAlgebraicallyClosedPointFieldStatement.{u, v, uL})
    (hgeom : EtaleSite.GeometricPointStatement.{u, v, max u (v + 1) uL}) :
    EtaleCoveringPointsStatement.{u, v} K := by
  intro X U S hS y
  obtain ⟨L, nL, uL', cL, aL, kL, hL⟩ := hfield K U.left
  obtain ⟨p, hp⟩ := hL (ULift.up y)
  let x := (localizedFieldPointFunctor L).map U.hom p
  obtain ⟨V, f, hf, q, hq⟩ :=
    (hgeom K L X x).2 S hS ⟨p, rfl⟩
  refine ⟨V, f, hf, ((localizedFieldPointProjection L).app V.left q.val).down, ?_⟩
  change localizedSpaceFunctor.map f.left
    ((localizedFieldPointProjection L).app V.left q.val).down = y
  have hq' : (localizedFieldPointFunctor L).map f.left q.val = p :=
    congrArg Subtype.val hq
  have hn := congrArg ULift.down
    (NatTrans.naturality_apply (localizedFieldPointProjection L) f.left q.val)
  change ((localizedFieldPointProjection L).app U.left
    ((localizedFieldPointFunctor L).map f.left q.val)).down =
      localizedSpaceFunctor.map f.left
        ((localizedFieldPointProjection L).app V.left q.val).down at hn
  rw [hq'] at hn
  exact hn.symm.trans (congrArg ULift.down hp)

/-- Select an arrow in a covering sieve and an ordinary point over the given
point, using the two explicit field-valued-point prerequisites. -/
def coveringPointLiftOfCommonPointFields
    (hfield : CommonAlgebraicallyClosedPointFieldStatement.{u, v, uL})
    (hgeom : EtaleSite.GeometricPointStatement.{u, v, max u (v + 1) uL})
    {X : LocalizedCategory.{u, v, v} (K := K)} {U : EtaleSite X}
    (S : Sieve U) (hS : S ∈ etaleTopology X U)
    (x : (EtaleSite.points X).obj U) :
    Σ V : EtaleSite X, Σ f : V ⟶ U,
      {y : (EtaleSite.points X).obj V //
        S f ∧ (EtaleSite.points X).map f y = x} :=
  Classical.choice <| by
    obtain ⟨V, f, hf, y, hy⟩ :=
      coveringPoints_of_commonPointFields hfield hgeom X S hS x
    exact ⟨⟨V, f, y, hf, hy⟩⟩

end Langlands.Analytic.SaturatedAtlasPresentation
