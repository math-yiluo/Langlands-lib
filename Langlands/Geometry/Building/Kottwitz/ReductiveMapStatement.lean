import Langlands.Geometry.Building.Kottwitz.ReductiveMap
import Mathlib.FieldTheory.IsSepClosed

/-! # Existence, independence and descent of reductive Kottwitz homomorphisms -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.Kottwitz

/-- KP §11.5: the simply-connected-derived construction through every actual cocenter. -/
def SimplyConnectedDerivedKottwitzStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)]
    [Algebra k (SeparableClosure F)] [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
    [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (hsc : HasSimplyConnectedDerivedGroup G),
    (∃! κ, IsSimplyConnectedDerivedKottwitzHom F k G hG κ) ∧
    IsSimplyConnectedDerivedKottwitzHom F k G hG
      (simplyConnectedDerivedKottwitz F k G hG hsc) ∧
    Function.Surjective (simplyConnectedDerivedKottwitz F k G hG hsc) ∧
    ∀ c : Cocenter k G,
      Function.Bijective (cocenterTargetMap F k G hG c) ∧
      ∀ κ, CocenterKottwitzLawAt F k G hG c κ ↔
        κ = simplyConnectedDerivedKottwitz F k G hG hsc

/-- KP Lemma 11.5.1: existence, uniqueness, independence and surjectivity through
actual z-extensions. The existence of a z-extension is a conclusion. -/
def ReductiveKottwitzExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)]
    [Algebra k (SeparableClosure F)] [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
    [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    Nonempty (ZExtension G) ∧
    (∃! κ, IsReductiveKottwitzHom F k G hG κ) ∧
    IsReductiveKottwitzHom F k G hG (reductiveKottwitz F k G hG) ∧
    Function.Surjective (reductiveKottwitz F k G hG) ∧
    (∀ hsc : HasSimplyConnectedDerivedGroup G,
      reductiveKottwitz F k G hG = simplyConnectedDerivedKottwitz F k G hG hsc) ∧
    ∀ z : ZExtension G,
      Function.Surjective
        (z.H.affinePointsTarget z.p (CommAlgCat.of k (UnramifiedClosure F))) ∧
      Function.Surjective
        (fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F)
          G hG z.H z.isZExtension.source_reductive z.p) ∧
      ∀ κ, ZExtensionKottwitzLawAt F k G hG z κ ↔ κ = reductiveKottwitz F k G hG

/-- KP Lemma 11.5.1: functoriality and compatibility with the original torus map. -/
def ReductiveKottwitzFunctorialityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)]
    [Algebra k (SeparableClosure F)] [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
    [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)],
    (∀ (H G : GroupScheme (Spec (CommRingCat.of k)))
      (hH : IsConnectedReductive H) (hG : IsConnectedReductive G) (f : H ⟶ G)
      (x : reductiveKPoints F k H),
      (reductiveKottwitz F k G hG
        (H.affinePointsTarget f (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd =
      fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F) G hG H hH f
        (reductiveKottwitz F k H hH x).toAdd) ∧
    (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp)
      (x : reductiveKPoints F k T.toGrp),
      torusInertiaComparison k (UnramifiedClosure F) (SeparableClosure F) T hT
        (reductiveKottwitz F k T.toGrp hT.isConnectedReductive_of_fieldSplitting x).toAdd =
      (torusKottwitz F k T hT x).toAdd)

/-- KP Lemma 11.5.1 and the following definition: residual equivariance and the
unique invariant-valued restriction to rational points. -/
def ReductiveKottwitzDescentStatement : Prop :=
  (∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)]
    [Algebra k (SeparableClosure F)] [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
    [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (σ : UnramifiedClosure F ≃ₐ[k] UnramifiedClosure F) (x : reductiveKPoints F k G),
    (reductiveKottwitz F k G hG
      (GaloisPoint.conjugate k (UnramifiedClosure F) G σ x)).toAdd =
    fundamentalGammaRepresentation k (UnramifiedClosure F) (SeparableClosure F) G hG σ
      (reductiveKottwitz F k G hG x).toAdd) ∧
  (∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    ReductiveKottwitzEquivariant F G hG ∧
    (∃! κ, IsReductiveKottwitzRestriction F G hG κ) ∧
    IsReductiveKottwitzRestriction F G hG (reductiveKottwitzRational F G hG))

end Langlands.Geometry.Building.Kottwitz
