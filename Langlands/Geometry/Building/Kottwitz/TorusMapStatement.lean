import Langlands.Geometry.Building.Kottwitz.TorusMap

/-! # Existence, independence and descent of torus Kottwitz homomorphisms -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.Kottwitz

/-- KP Proposition 11.1.1: existence, uniqueness, splitting-field independence and surjectivity.
The field `k` records a field of definition for the original group scheme. -/
def TorusKottwitzExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)]
    [Algebra k (SeparableClosure F)] [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
    [Normal k (UnramifiedClosure F)]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp),
    letI : IsAffine T.X.left := torusIsAffine k T hT;
    (∃! κ, IsTorusKottwitzHom F k T κ) ∧
    IsTorusKottwitzHom F k T (torusKottwitz F k T hT) ∧
    Function.Surjective (torusKottwitz F k T hT) ∧
    ∀ (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
      [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
      (hL : IsSplitTorus ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp),
      Function.Surjective (GaloisPoint.relativeNorm k (UnramifiedClosure F) L T) ∧
      ∀ κ, TorusNormLawAt F k T L hL κ ↔ κ = torusKottwitz F k T hT

/-- KP Proposition 11.1.1 and the ensuing restriction to `F`-points. -/
def TorusKottwitzDescentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (hT : IsTorus T.toGrp),
    TorusKottwitzEquivariant F T hT ∧
    (∃! κ, IsTorusKottwitzRestriction F T hT κ) ∧
    IsTorusKottwitzRestriction F T hT (torusKottwitzRational F T hT)

end Langlands.Geometry.Building.Kottwitz
