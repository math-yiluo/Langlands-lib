import Langlands.Geometry.Building.Kottwitz.InertiaCoinvariants
import Langlands.Geometry.Building.Kottwitz.NormalizedValuation
import Langlands.Geometry.Building.Kottwitz.SplitValuation
import Langlands.GroupScheme.GaloisPointTowerBaseChange
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Torus.ConnectedReductive

/-! # The norm characterization of the torus Kottwitz homomorphism -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.Kottwitz

section CocharacterExtension

variable (k L E : Type u) [Field k] [Field L] [Field E]
  [Algebra k L] [Algebra k E] [Algebra L E] [IsScalarTower k L E]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- Extend actual cocharacters from `T_L` to `T_E`, using the canonical tower comparison. -/
def extendGeometricCocharacters :
    cocharacterLattice ((CommGroupScheme.baseChange (baseMap k L)).obj T) →+
      geometricCocharacters k E T :=
  (cocharacterLattice.congr
    (CommGroupScheme.isoOfGroupIso (towerBaseChangeIso k L E T.toGrp))).toAddMonoidHom.comp
      (cocharacterLattice.baseChange (baseMap L E)
        ((CommGroupScheme.baseChange (baseMap k L)).obj T))

end CocharacterExtension

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

variable (k : Type u) [Field k]
  [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)] [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- The geometric target for a torus over `k`, evaluated over the maximal unramified field. -/
abbrev TorusTarget := torusInertiaCoinvariants k (UnramifiedClosure F) (SeparableClosure F) T

/-- The original group scheme's `(UnramifiedClosure F)`-coefficient points. -/
abbrev torusKPoints := affinePoints T.toGrp (CommAlgCat.of k (UnramifiedClosure F))

private instance intermediateScalarTower
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)) :
    IsScalarTower k L (SeparableClosure F) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

section Affine

variable [IsAffine T.X.left]

/-- The KP norm square for one finite Galois splitting extension. -/
def TorusNormLawAt
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)) [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
    (hL : IsSplitTorus ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp)
    (κ : torusKPoints F k T →* Multiplicative (TorusTarget F k T)) : Prop :=
  ∀ t : rationalPoints ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp,
    κ (GaloisPoint.relativeNorm k (UnramifiedClosure F) L T (baseChangeCoeffEquiv k L T.toGrp t)) =
      Multiplicative.ofAdd
        (inertiaProjection k (UnramifiedClosure F) (SeparableClosure F) (cocharacterLattice.galoisRepresentation k (SeparableClosure F) T)
          (extendGeometricCocharacters k L (SeparableClosure F) T
            (splitValuation ((CommGroupScheme.baseChange (baseMap k L)).obj T) hL
              (normalizedIntermediateValuation F L) t).toAdd))

/-- The norm characterization for every finite Galois splitting extension. -/
def IsTorusKottwitzHom
    (κ : torusKPoints F k T →* Multiplicative (TorusTarget F k T)) : Prop :=
  ∀ (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)) [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
    (hL : IsSplitTorus ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp),
      TorusNormLawAt F k T L hL κ

end Affine

theorem torusIsAffine (hT : IsTorus T.toGrp) : IsAffine T.X.left := by
  let : IsAffineHom T.X.hom :=
    (IsTorus.isConnectedReductive_of_fieldSplitting hT).isAffineHom
  exact isAffine_of_isAffineHom T.X.hom

variable (hT : IsTorus T.toGrp)

/-- The actual map selected by the norm characterization.
Its unconditional specification is `TorusKottwitzExistenceStatement`. -/
def torusKottwitz :
    torusKPoints F k T →* Multiplicative (TorusTarget F k T) := by
  letI : IsAffine T.X.left := torusIsAffine k T hT
  exact Classical.epsilon (IsTorusKottwitzHom F k T)

/-- The epsilon construction has the norm law whenever a homomorphism with that law exists. -/
theorem torusKottwitz_spec
    (h : letI : IsAffine T.X.left := torusIsAffine k T hT;
      ∃ κ, IsTorusKottwitzHom F k T κ) :
    letI : IsAffine T.X.left := torusIsAffine k T hT;
      IsTorusKottwitzHom F k T (torusKottwitz F k T hT) :=
  Classical.epsilon_spec h

section Descent

variable (S : CommGroupScheme (Spec (CommRingCat.of F)))

/-- Residual invariants in the actual inertia quotient for an `F`-torus. -/
abbrev TorusInvariantTarget :=
  inertiaInvariants F (UnramifiedClosure F) (SeparableClosure F)
    (cocharacterLattice.galoisRepresentation F (SeparableClosure F) S)

/-- Forget that a class is fixed by the residual Galois group. -/
def torusInvariantInclusion :
    Multiplicative (TorusInvariantTarget F S) →*
      Multiplicative (TorusTarget F F S) :=
  (TorusInvariantTarget F S).subtype.toAddMonoidHom.toMultiplicative

variable (hS : IsTorus S.toGrp)

/-- Equivariance under the actual residual automorphism group `Gal(K/F)`. -/
def TorusKottwitzEquivariant : Prop :=
  ∀ (σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F) (t : torusKPoints F F S),
    (torusKottwitz F F S hS
      (GaloisPoint.conjugate F (UnramifiedClosure F) S.toGrp σ t)).toAdd =
    torusGammaRepresentation F (UnramifiedClosure F) (SeparableClosure F) S σ
      (torusKottwitz F F S hS t).toAdd

/-- A rational-point homomorphism is the restriction of the constructed `K`-point map. -/
def IsTorusKottwitzRestriction
    (κ : rationalPoints S.toGrp →* Multiplicative (TorusInvariantTarget F S)) : Prop :=
  ∀ t, torusInvariantInclusion F S (κ t) =
    torusKottwitz F F S hS
      (GaloisPoint.extend F (UnramifiedClosure F) S.toGrp
        (rationalCoeffEquiv F S.toGrp t))

/-- The torus Kottwitz homomorphism on `F`-points, selected as an invariant-valued restriction.
`TorusKottwitzDescentStatement` states its unconditional restriction law. -/
def torusKottwitzRational :
    rationalPoints S.toGrp →* Multiplicative (TorusInvariantTarget F S) :=
  Classical.epsilon (IsTorusKottwitzRestriction F S hS)

end Descent

end Langlands.Geometry.Building.Kottwitz
