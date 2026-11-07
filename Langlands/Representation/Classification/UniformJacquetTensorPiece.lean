import Langlands.Representation.Classification.UniformRefinementLeviTransport
import Langlands.Representation.Geometric.WholeLeviPieceTransport
import Langlands.Representation.CuspidalSupport.LeviAssociation

/-! A uniform-target geometric piece from supplied blockwise Jacquet tensors. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification.UniformJacquetTensorPiece

open GeneralLinear Geometric CuspidalSupport

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

set_option maxHeartbeats 1000000 in
/-- A minimal geometric piece with uniform target is the specified tensor if
its source blocks have the corresponding Jacquet tensors. -/
def pieceEquiv
    {m r : ℕ} (hr : 0 < r) (B : BlockShape (m * r))
    (blocks : letI := T.topology;
      ∀ j : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size j) F.Carrier))
    (w : Equiv.Perm (Fin (m * r)))
    (hw : IsMinimalRepresentative B (BlockShape.uniform m r hr) w)
    (S : BlockRefinement B) (R : BlockRefinement (BlockShape.uniform m r hr))
    (hS : sourceLevi F.Carrier B (BlockShape.uniform m r hr) w =
      refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier (BlockShape.uniform m r hr) B w⁻¹ =
      refinedLevi F.Carrier (BlockShape.uniform m r hr) R)
    (hdiv : ∀ j i, r ∣ (S j).size i)
    (X : letI := T.topology;
      Fin m → SmoothRep.{0, uF, uW} ℂ (GeneralLinear r F.Carrier))
    (hX : letI := T.topology; ∀ j,
      Nonempty ((T.normalizedJacquet (S j) (blocks j).representation).Equiv
        (FiniteTensor.external (fun i =>
          ((ShuffleRefinement.source_size_eq_of_dvd hr B w S hS j i (hdiv j i)).symm ▸
            X (ShuffleRefinement.refinementTargetIndex hr B w S j i) :
              SmoothRep.{0, uF, uW} ℂ (GeneralLinear ((S j).size i) F.Carrier)).representation)))) :
    letI := T.topology
    ((geometricPieceFunctor T B (BlockShape.uniform m r hr)
        w S R hS hR).obj (FiniteTensor.externalSmoothObject blocks)).ρ.Equiv
      (FiniteTensor.external (fun t => (X t).representation)) := by
  let := T.topology
  let C := BlockShape.uniform m r hr
  have hc := ShuffleRefinement.conjugatesLevi_flatten_uniform hr B w S hS hdiv
  let τ := fun j i =>
    ((ShuffleRefinement.source_size_eq_of_dvd hr B w S hS j i (hdiv j i)).symm ▸
      X (ShuffleRefinement.refinementTargetIndex hr B w S j i) :
        SmoothRep.{0, uF, uW} ℂ (GeneralLinear ((S j).size i) F.Carrier))
  have H : ∀ j, (T.normalizedJacquet (S j) (blocks j).representation).Equiv
      (FiniteTensor.external (fun i => (τ j i).representation)) := fun j => (hX j).some
  let X' := FiniteTensor.external
    (fun j => FiniteTensor.external (fun i => (τ j i).representation))
  let e1 := wholeLeviGeometricPieceEquiv T B C w S R hS hR hc
    (FiniteTensor.externalSmoothObject blocks)
  let e2 := (RefinedJacquetTensor.jacquetEquiv T B S (fun j => (blocks j).obj)).trans
    (FiniteTensorFiltration.compCongr (FiniteTensorFiltration.externalCongr H)
      (refinedLeviEquiv F.Carrier B S).symm.toMonoidHom)
  let e3 : Representation.Equiv ((X'.comp (refinedLeviEquiv F.Carrier B S).symm.toMonoidHom).comp
      (flattenedLeviEquiv F.Carrier B S).toMonoidHom)
      (X'.comp (flattenedLeviProductEquiv F.Carrier B S).toMonoidHom) :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun g => by
      apply LinearMap.ext
      intro v
      simp [flattenedLeviEquiv])
  let e4 := CuspidalSupport.transportEquiv w hc
    ((FiniteTensorFiltration.compCongr e2
      (flattenedLeviEquiv F.Carrier B S).toMonoidHom).trans e3)
  let e5 := (ShuffleRefinement.uniformRefinementTensorEquiv F T hr B w S hS hw hdiv X).symm
  exact e1.trans (e4.trans e5)

end Langlands.Classification.UniformJacquetTensorPiece
