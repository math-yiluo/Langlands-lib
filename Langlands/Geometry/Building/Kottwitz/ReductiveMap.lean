import Langlands.Geometry.Building.Kottwitz.FundamentalGroup
import Langlands.Geometry.Building.Kottwitz.TorusMap
import Langlands.GroupScheme.Derived.CocenterQuotientProof
import Langlands.GroupScheme.ZExtension

/-! # Kottwitz homomorphisms through actual cocenters and z-extensions -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.Kottwitz

/-- An actual quotient by the full scheme-theoretic derived subgroup. -/
structure Cocenter (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  quotient : G ⟶ torus.toGrp
  isTorus : IsTorus torus.toGrp
  isQuotient : RelativeRoot.IsFppfQuotient (derivedSubgroup G) quotient

/-- Existence of the actual cocenter is already proved in the Library. -/
theorem nonempty_cocenter (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    Nonempty (Cocenter k G) := by
  let a := chosenChoice k G hG
  obtain ⟨Q, q, _, hq, hQ, _⟩ := cocenterQuotientExistence k G a.derived
    a.derivedInclusion hG a.isCover.isDerivedSubgroup
  refine ⟨⟨Q, q, hQ, ?_⟩⟩
  simpa only [a.isCover.isDerivedSubgroup.2] using hq

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (k : Type u) [Field k]
  [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
  [Normal k (UnramifiedClosure F)]
  (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)

/-- The original group's points with coefficients in the actual maximal unramified field. -/
abbrev reductiveKPoints := affinePoints G (CommAlgCat.of k (UnramifiedClosure F))

/-- The target `π₁(G)_I` of the Kottwitz map. -/
abbrev ReductiveTarget :=
  FundamentalInertia k (UnramifiedClosure F) (SeparableClosure F) G hG

/-- The actual map to the cocenter's torus inertia target. -/
def cocenterTargetMap (c : Cocenter k G) :
    ReductiveTarget F k G hG →ₗ[ℤ] TorusTarget F k c.torus :=
  (torusInertiaComparison k (UnramifiedClosure F) (SeparableClosure F) c.torus c.isTorus).comp
    (fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F)
      c.torus.toGrp c.isTorus.isConnectedReductive_of_fieldSplitting G hG c.quotient)

/-- The defining square of §11.5 for a simply-connected-derived group and one actual cocenter. -/
def CocenterKottwitzLawAt (c : Cocenter k G)
    (κ : reductiveKPoints F k G →* Multiplicative (ReductiveTarget F k G hG)) : Prop :=
  ∀ x, cocenterTargetMap F k G hG c (κ x).toAdd =
    (torusKottwitz F k c.torus c.isTorus
      (G.affinePointsTarget c.quotient (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd

/-- The simply-connected-derived map is characterized by every actual cocenter square. -/
def IsSimplyConnectedDerivedKottwitzHom
    (κ : reductiveKPoints F k G →* Multiplicative (ReductiveTarget F k G hG)) : Prop :=
  ∀ c : Cocenter k G, CocenterKottwitzLawAt F k G hG c κ

/-- Kottwitz for a group with simply connected derived subgroup, selected through its
actual cocenter. Unique existence and independence are separate unconditional targets. -/
def simplyConnectedDerivedKottwitz (_hsc : HasSimplyConnectedDerivedGroup G) :
    reductiveKPoints F k G →* Multiplicative (ReductiveTarget F k G hG) :=
  Classical.epsilon (IsSimplyConnectedDerivedKottwitzHom F k G hG)

/-- The z-extension square for the actual projection and induced inertia homomorphism. -/
def ZExtensionKottwitzLawAt (z : ZExtension G)
    (κ : reductiveKPoints F k G →* Multiplicative (ReductiveTarget F k G hG)) : Prop :=
  ∀ x : reductiveKPoints F k z.H,
    (κ (z.H.affinePointsTarget z.p (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd =
      fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F)
        G hG z.H z.isZExtension.source_reductive z.p
        (simplyConnectedDerivedKottwitz F k z.H z.isZExtension.source_reductive
          z.isZExtension.derived_simplyConnected x).toAdd

/-- The defining z-extension characterization includes nonemptiness, and requires
commutativity for every z-extension, so it cannot hold vacuously. -/
def IsReductiveKottwitzHom
    (κ : reductiveKPoints F k G →* Multiplicative (ReductiveTarget F k G hG)) : Prop :=
  Nonempty (ZExtension G) ∧ ∀ z : ZExtension G, ZExtensionKottwitzLawAt F k G hG z κ

/-- The actual reductive Kottwitz homomorphism, characterized by the z-extension
construction of KP §11.5 and Lemma 11.5.1. -/
def reductiveKottwitz :
    reductiveKPoints F k G →* Multiplicative (ReductiveTarget F k G hG) :=
  Classical.epsilon (IsReductiveKottwitzHom F k G hG)

section Restriction
variable (S : GroupScheme (Spec (CommRingCat.of F))) (hS : IsConnectedReductive S)

/-- The invariant-valued target of the map on `F`-rational points. -/
abbrev ReductiveInvariantTarget :=
  FundamentalInvariants F (UnramifiedClosure F) (SeparableClosure F) S hS

/-- The inclusion `A^Γ → A`. -/
def reductiveInvariantInclusion :
    Multiplicative (ReductiveInvariantTarget F S hS) →*
      Multiplicative (ReductiveTarget F F S hS) :=
  (ReductiveInvariantTarget F S hS).subtype.toAddMonoidHom.toMultiplicative

/-- Residual Galois equivariance for the constructed map. -/
def ReductiveKottwitzEquivariant : Prop :=
  ∀ (σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F) (x : reductiveKPoints F F S),
    (reductiveKottwitz F F S hS
      (GaloisPoint.conjugate F (UnramifiedClosure F) S σ x)).toAdd =
    fundamentalGammaRepresentation F (UnramifiedClosure F) (SeparableClosure F) S hS σ
      (reductiveKottwitz F F S hS x).toAdd

/-- Restriction from actual `K`-coefficient points to actual rational points. -/
def IsReductiveKottwitzRestriction
    (κ : rationalPoints S →* Multiplicative (ReductiveInvariantTarget F S hS)) : Prop :=
  ∀ x, reductiveInvariantInclusion F S hS (κ x) =
    reductiveKottwitz F F S hS
      (GaloisPoint.extend F (UnramifiedClosure F) S (rationalCoeffEquiv F S x))

/-- The rational Kottwitz map selected as the invariant-valued restriction. -/
def reductiveKottwitzRational :
    rationalPoints S →* Multiplicative (ReductiveInvariantTarget F S hS) :=
  Classical.epsilon (IsReductiveKottwitzRestriction F S hS)

end Restriction

end Langlands.Geometry.Building.Kottwitz
