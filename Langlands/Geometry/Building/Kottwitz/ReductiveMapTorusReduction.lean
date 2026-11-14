import Langlands.Geometry.Building.Kottwitz.ReductiveMapStructuralReduction
import Langlands.Geometry.Building.Kottwitz.TorusFundamentalComparisonProof
import Langlands.Geometry.Building.Kottwitz.TorusInertiaComparisonProof
import Langlands.Geometry.Building.Kottwitz.TorusMapProof
import Langlands.Geometry.Building.Kottwitz.TorusNormNaturality
import Langlands.GroupScheme.AlgebraicFundamentalGroupComparisonProof
import Langlands.GroupScheme.AlgebraicFundamentalGroupMapNaturality
import Langlands.GroupScheme.ZExtensionExistenceProof

/-! # Reductive Kottwitz descent from torus existence and remaining structural inputs -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

variable
    (hmap : FundamentalInertiaMapStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (k : Type u) [Field k]
    [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
    [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
    [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)]

include hmap

/-- Choosing the already existing actual cocenters removes supplied-cocenter
hypotheses from the simply-connected-derived naturality reduction. -/
theorem simplyConnectedDerivedKottwitzNaturalAt_of_torus_existence
    (H J : GroupScheme (Spec (CommRingCat.of k)))
    (hH : IsConnectedReductive H) (hJ : IsConnectedReductive J)
    (hscH : HasSimplyConnectedDerivedGroup H) (hscJ : HasSimplyConnectedDerivedGroup J)
    (f : H ⟶ J) :
    SimplyConnectedDerivedKottwitzNaturalAt F k H J hH hJ hscH hscJ f := by
  have hfund := algebraicFundamentalGroupMap_of_comparison
    algebraicFundamentalGroupComparison.{u}
  have hsc := simplyConnectedDerivedKottwitz_of_norm_inputs
    algebraicFundamentalGroupComparison hfund torusFundamentalComparison_proof
    hmap torusInertiaComparison_proof torusKottwitzExistence
  obtain ⟨cH⟩ := nonempty_cocenter k H hH
  obtain ⟨cJ⟩ := nonempty_cocenter k J hJ
  intro x
  exact simplyConnectedDerivedKottwitz_natural_of_torus_naturality
    algebraicFundamentalGroupComparison hfund torusFundamentalComparison_proof hmap
    torusInertiaComparison_proof
    F k H J hH hJ cH cJ f hsc hscH hscJ
    (torusKottwitz_natural_of_existence F k cH.isTorus cJ.isTorus
      (cH.map cJ hH f) torusKottwitzExistence) x

/-- Torus existence supplies all upstairs naturality and kernel annihilation;
z-extension existence is supplied by the published arbitrary-field theorem. -/
theorem reductiveKottwitzExistenceAt_of_torus_existence
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (hp : ∀ z : ZExtension G, Function.Surjective (zExtensionPointMap F k G z))
    (ht : ∀ z : ZExtension G, Function.Surjective
      (fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F)
        G hG z.H z.isZExtension.source_reductive z.p))
    (hrefine : ∀ z z' : ZExtension G, ∃ w : ZExtension G,
      ∃ r : w.H ⟶ z.H, ∃ r' : w.H ⟶ z'.H,
        r ≫ z.p = w.p ∧ r' ≫ z'.p = w.p) :
    Nonempty (ZExtension G) ∧
    (∃! κ, IsReductiveKottwitzHom F k G hG κ) ∧
    IsReductiveKottwitzHom F k G hG (reductiveKottwitz F k G hG) ∧
    Function.Surjective (reductiveKottwitz F k G hG) ∧
    (∀ hscG : HasSimplyConnectedDerivedGroup G,
      reductiveKottwitz F k G hG = simplyConnectedDerivedKottwitz F k G hG hscG) ∧
    ∀ z : ZExtension G,
      Function.Surjective (zExtensionPointMap F k G z) ∧
      Function.Surjective
        (fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F)
          G hG z.H z.isZExtension.source_reductive z.p) ∧
      ∀ κ, ZExtensionKottwitzLawAt F k G hG z κ ↔ κ = reductiveKottwitz F k G hG :=
by
  have hfund := algebraicFundamentalGroupMap_of_comparison
    algebraicFundamentalGroupComparison.{u}
  have hsc := simplyConnectedDerivedKottwitz_of_norm_inputs
    algebraicFundamentalGroupComparison hfund torusFundamentalComparison_proof
    hmap torusInertiaComparison_proof torusKottwitzExistence
  exact reductiveKottwitzExistenceAt_of_naturality F k G hG hfund hsc hmap
    (simplyConnectedDerivedKottwitzNaturalAt_of_torus_existence
      hmap F k) (zExtensionExistence k G hG) hp ht hrefine

end Langlands.Geometry.Building.Kottwitz
