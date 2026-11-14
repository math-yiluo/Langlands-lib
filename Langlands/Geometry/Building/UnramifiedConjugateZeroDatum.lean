import Langlands.Geometry.Building.UnramifiedConjugateTorusTransport
import Langlands.Geometry.Building.SemilinearTorusNormFieldIso

/-! # Conjugation of the torus and splitting field in a zero datum -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (E : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G))
  (σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F)

/-- Conjugate the torus and its splitting field, retaining the supplied derived cover
of the unchanged ambient group. -/
def UnramifiedZeroDatum.galoisTransport :
    UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G) where
  T := (CommGroupScheme.baseChange (galoisBaseMap F (UnramifiedClosure F) σ)).obj E.T
  isAffine := by
    change IsAffine (CategoryTheory.Limits.pullback E.T.X.hom _)
    infer_instance
  i := (GroupScheme.baseChange (galoisBaseMap F (UnramifiedClosure F) σ)).map E.i ≫
    (descentBaseChangeIso (baseMap F (UnramifiedClosure F))
      (galoisBaseMap F (UnramifiedClosure F) σ)
      (galoisBaseMap_over F (UnramifiedClosure F) σ) G).hom
  isMaximallySplitMaximalTorus :=
    (E.isMaximallySplitMaximalTorus.baseChange_fieldIso σ.toRingEquiv).comp_iso
      (descentBaseChangeIso (baseMap F (UnramifiedClosure F))
        (galoisBaseMap F (UnramifiedClosure F) σ)
        (galoisBaseMap_over F (UnramifiedClosure F) σ) G)
  L := unramifiedConjugateField F σ E.L
  isSplitTorus := isSplitTorus_fieldIso_square σ.toRingEquiv
    (unramifiedConjugateFieldEquiv F σ E.L)
    (unramifiedConjugateFieldEquiv_commutes F σ E.L) E.T E.isSplitTorus
  D := E.D
  C := E.C
  d := E.d
  π := E.π
  isSimplyConnectedDerivedCover := E.isSimplyConnectedDerivedCover

/-- The coefficient section map preserves the bounded norm image in the transported
zero datum. -/
theorem UnramifiedZeroDatum.map_torusIwahori_le_galoisTransport :
    E.torusIwahori.map
        (baseChangeSectionHom (galoisBaseMap F (UnramifiedClosure F) σ) E.T.toGrp) ≤
      (UnramifiedZeroDatum.galoisTransport F G E σ).torusIwahori := by
  exact map_torusNormIwahori_le_fieldIso_square σ.toRingEquiv
    (unramifiedConjugateFieldEquiv F σ E.L)
    (unramifiedConjugateFieldEquiv_commutes F σ E.L)
    (intermediateValuation F E.L)
    (intermediateValuation F (unramifiedConjugateField F σ E.L))
    (unramifiedConjugateFieldEquiv_valuation_isEquiv F σ E.L) E.T

end Langlands.Geometry.Building
