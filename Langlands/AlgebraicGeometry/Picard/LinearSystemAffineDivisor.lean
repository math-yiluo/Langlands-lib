import Langlands.AlgebraicGeometry.Picard.LinearSystemUniversalDivisor
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveLocal
import Langlands.RingTheory.Grassmannian.ProperFinitePresentation

/-! # The universal divisor of the linear system is a relative effective Cartier divisor -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule

open Scheme.TwoAffineOpenCover SectionZeroIdeal
open Module.Grassmannian.ProjectiveEmbedding (Rep InChart)

section Generators

variable {X : Scheme.{u}} {L : LineBundle X} {σ : Γ(L.obj, ⊤)}

/-- **The zero ideal of a regular section has local regular generators.** -/
lemma exists_local_regular_generator (hσ : IsRegularSection L σ) (z : X) :
    ∃ U : X.affineOpens, z ∈ U.1 ∧ ∃ a : Γ(X, U.1),
      (zeroIdeal L σ).ideal U = Ideal.span {a} ∧ IsSMulRegular Γ(X, U.1) a := by
  obtain ⟨U, hzU, t, ht⟩ := exists_affine_frame L z
  refine ⟨U, hzU, frameEquiv ht (res L σ U.1), zeroIdeal_ideal_of_equiv L σ U (frameEquiv ht), ?_⟩
  intro c d hcd
  change frameEquiv ht (res L σ U.1) * c = frameEquiv ht (res L σ U.1) * d at hcd
  rw [← sub_eq_zero]
  apply hσ U.1
  rw [eq_frameEquiv_smul ht (res L σ U.1), smul_smul, sub_mul, mul_comm c, mul_comm d, hcd,
    sub_self, zero_smul]

end Generators

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)}
  [IsProper π] [Flat π] [GeometricallyIntegral π] {L : LineBundle X}
  {𝒰 : X.OrderedAffineCover} (e : ∀ i, Γ(L.obj, 𝒰.U i))
  (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (𝒰.U i)) (C : CechRep π L.obj 𝒰)
  (D : Rep R C.Q 1)

instance : Module.Finite R C.Q := by
  unfold CechRep.Q Langlands.CommutativeAlgebra.CokernelDualHom.Q
  infer_instance

include he in
/-- **The universal divisor is relative effective Cartier over the Grassmannian.** -/
theorem isRelativeEffectiveCartierIdeal_universal {W : (pullback π D.p).IdealSheafData}
    (hW : ∀ {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ D.Gr)
      (hk : k ≫ D.p = specMap R B) (hP : LinSys.InSomeChart D k),
      W.comap (ptMap π D.p k hk) = LinSys.FOf L D k hk hP) :
    IsRelativeEffectiveCartierIdeal (pullback.snd π D.p) W := by
  have : IsProper D.p := D.isProper_p
  have : IsLocallyNoetherian D.Gr := LocallyOfFiniteType.isLocallyNoetherian D.p
  let P := LinSys.pointIdeals e he D
  refine RelativeEffectiveLocal.isRelativeEffectiveCartierIdeal_of_cover (pullback.snd π D.p) W
    (fun O : P.Adm => P.pieceι O) (fun O => pullback.snd π (@specMap R Γ(D.Gr, O.1.1) _ _
      (affAlg D.p O.1))) (fun O => affPt O.1)
    (fun O => @ptMap_snd R _ X π D.Gr D.p Γ(D.Gr, O.1.1) _ (affAlg D.p O.1) (affPt O.1)
      (affPt_comp D.p O.1)) (fun x => ?_)
    (fun O => ?_) (fun O z => ?_)
  · exact ⟨P.openCover.idx x, P.openCover.covers x⟩
  · let _ := affAlg D.p O.1
    have : IsNoetherianRing Γ(D.Gr, O.1.1) := IsLocallyNoetherian.component_noetherian O.1
    have h := hW (B := Γ(D.Gr, O.1.1)) (affPt O.1) (affPt_comp D.p O.1) O.2
    show IsRelativeEffectiveCartierIdeal _ (W.comap (ptMap π D.p (affPt O.1) (affPt_comp D.p O.1)))
    rw [h]
    exact (homEquivSections_regular_and_relativeEffective e he C _
      (LinSys.span_range_vOf D _ _ O.2)).2
  · let _ := affAlg D.p O.1
    have : IsNoetherianRing Γ(D.Gr, O.1.1) := IsLocallyNoetherian.component_noetherian O.1
    have h := hW (B := Γ(D.Gr, O.1.1)) (affPt O.1) (affPt_comp D.p O.1) O.2
    obtain ⟨U', hz, a, ha, hreg⟩ := exists_local_regular_generator
      (homEquivSections_regular_and_relativeEffective e he C _
        (LinSys.span_range_vOf D _ _ O.2)).1 z
    refine ⟨U', hz, a, ?_, hreg⟩
    have h' : W.comap (P.pieceι O) = LinSys.FOf L D (affPt O.1) (affPt_comp D.p O.1) O.2 := h
    rw [h']
    exact ha

end Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule
