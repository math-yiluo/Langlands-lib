import Langlands.AlgebraicGeometry.UniformLangWeilHenselianLifts
import Langlands.Global.CompletionIntegersSmoothPointLifting
import Langlands.Global.CompletionResidueBounds
import Langlands.Global.FunctionFieldAdelesLocallyCompactProof

/-! # Actual integral lifts outside a finite set of global places -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology

/-- Uniform exact integral lifts at all actual curve places outside one
finite set. The original coefficient algebra may be supplied separately
at each place where an integral lift is requested. -/
def curvePlaceAlmostAllIntegralPointLifts
    (hLW : UniformLangWeilStatement.{u})
    (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (C : Type u) [CommRing C] (B Y : Over (Spec (CommRingCat.of C)))
    (f : Y ⟶ B) (d : ℕ)
    (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B.left))
    (hBqc : CompactSpace B.left) (hsmooth : Smooth f.left)
    (hsep : _root_.AlgebraicGeometry.IsSeparated f.left) (hsurj : Surjective f.left)
    (hft : LocallyOfFiniteType f.left) (hqc : QuasiCompact f.left)
    (hconn : GeometricallyConnected f.left)
    (hdim : ∀ b : B.left, SchemeFiberGeometry.HasPureDimension (f.left.fiber b) d) :
    Σ S : Finset (AlgebraicCurve.Place k F),
      (v : AlgebraicCurve.Place k F) → v ∉ S →
        [Algebra C (curvePlaceCompletionIntegers v)] →
        (p : RingPoint C B (curvePlaceCompletionIntegers v)) →
        {a : RingPoint C Y (curvePlaceCompletionIntegers v) // a ≫ f = p} := by
  let lifts := uniformLangWeilLargeHenselianRingPointLifts hLW C B Y f d
    hBft hBqc hsmooth hsep hsurj hft hqc hconn hdim
  refine ⟨curvePlaceSmallCompletionResiduePlaces k F (lifts.1.1 ^ 2),
    fun v hv _ p => ?_⟩
  let : HenselianLocalRing (curvePlaceCompletionIntegers v) :=
    curvePlaceCompletionIntegers_henselian v
  let : Finite (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v)) :=
    curvePlaceCompletionResidue_finite k F v
  exact lifts.2 (curvePlaceCompletionIntegers v)
    (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v))
    (IsScalarTower.toAlgHom C (curvePlaceCompletionIntegers v)
      (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v)))
    IsLocalRing.residue_surjective
    (curvePlaceSmallCompletionResiduePlaces_lt k F _ v hv) p

/-- Uniform exact integral lifts at all finite places of a number field
outside one finite set, retaining the original coefficient base. -/
def numberFieldAlmostAllIntegralPointLifts
    (hLW : UniformLangWeilStatement.{u})
    (K : Type u) [Field K] [NumberField K]
    (C : Type u) [CommRing C] (B Y : Over (Spec (CommRingCat.of C)))
    (f : Y ⟶ B) (d : ℕ)
    (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B.left))
    (hBqc : CompactSpace B.left) (hsmooth : Smooth f.left)
    (hsep : _root_.AlgebraicGeometry.IsSeparated f.left) (hsurj : Surjective f.left)
    (hft : LocallyOfFiniteType f.left) (hqc : QuasiCompact f.left)
    (hconn : GeometricallyConnected f.left)
    (hdim : ∀ b : B.left, SchemeFiberGeometry.HasPureDimension (f.left.fiber b) d) :
    Σ S : Finset (FinitePlace K),
      (v : FinitePlace K) → v ∉ S →
        [Algebra C (v.adicCompletionIntegers K)] →
        (p : RingPoint C B (v.adicCompletionIntegers K)) →
        {a : RingPoint C Y (v.adicCompletionIntegers K) // a ≫ f = p} := by
  let lifts := uniformLangWeilLargeHenselianRingPointLifts hLW C B Y f d
    hBft hBqc hsmooth hsep hsurj hft hqc hconn hdim
  refine ⟨finitePlaceSmallCompletionResiduePlaces K (lifts.1.1 ^ 2),
    fun v hv _ p => ?_⟩
  let : HenselianLocalRing (v.adicCompletionIntegers K) :=
    adicCompletionIntegers_henselian (NumberField.RingOfIntegers K) K v
  exact lifts.2 (v.adicCompletionIntegers K)
    (IsLocalRing.ResidueField (v.adicCompletionIntegers K))
    (IsScalarTower.toAlgHom C (v.adicCompletionIntegers K)
      (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
    IsLocalRing.residue_surjective
    (finitePlaceSmallCompletionResiduePlaces_lt K _ v hv) p

end Langlands.Global
