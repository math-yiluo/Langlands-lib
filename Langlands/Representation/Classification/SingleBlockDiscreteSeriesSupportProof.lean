import Langlands.Representation.Classification.SingleBlockDiscreteSeriesSupportStatement
import Langlands.Representation.Classification.DiscreteSeriesPositiveRootSupportProof
import Langlands.Representation.Classification.InverseTransposeAnalyticProof
import Langlands.Representation.CuspidalSupport.AssociationReduction

/-!
# Single-block unitary cuspidal support on the original GL carrier

Transport the all-Haar square-integrability predicate through the actual
single-block continuous group equivalence, apply the product-Levi support
theorem, and pull its surjective map back to the original GL action.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uF uV

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (C : BlockShape n) (hC : C.length = 1)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

include hC

/-- The original all-Haar analytic predicate is equivalent to its pullback
to any actual single-block Levi, without changing the representation carrier. -/
theorem isLeviSquareIntegrable_singleBlock_iff
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    RelativeRegularComparison.IsLeviSquareIntegrable T C
      (Rep.of (ρ.comp (C.leviEmbedding F.Carrier))) ↔ T.IsSquareIntegrable ρ := by
  let := T.topology
  let := T.leviTopologicalGroup C
  have := T.generalLinearTopologicalGroup n
  have : IsModuleTopology (Padic p) F.Carrier := T.moduleTopology
  have : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  let e := C.singleBlockLeviEquivContinuous hC F.Carrier
  constructor
  · intro hρ μ _
    let : MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) :=
      borel _
    have : BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) := ⟨rfl⟩
    have hback := isSquareIntegrableModCenter_comp_continuousMulEquiv
      (ρ.comp e.toMonoidHom) e.symm μ (hρ _)
    have hcancel : (ρ.comp e.toMonoidHom).comp e.symm.toMonoidHom = ρ := by
      ext g v
      change ρ (e (e.symm g)) v = ρ g v
      rw [e.apply_symm_apply]
    rwa [hcancel] at hback
  · intro hρ _ _ μ _
    exact isSquareIntegrableModCenter_comp_continuousMulEquiv ρ e μ (hρ _)

end PadicField.TopologicalData

/-- The verified product-Levi support theorem specializes to the given GL
representation, with the same strict parameter and an actual quotient map. -/
theorem glSingleBlockDiscreteSeriesSupport :
    GLSingleBlockDiscreteSeriesSupportStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n hn C hC V _ _ ρ hirr hsq
  let e := C.singleBlockLeviEquiv hC F.Carrier
  have hpullirr : Representation.IsIrreducible (ρ.comp (C.leviEmbedding F.Carrier)) :=
    (CuspidalSupport.isIrreducible_comp_mulEquiv_iff ρ e).mpr hirr
  have hpullsq : RelativeRegularComparison.IsLeviSquareIntegrable T C
      (Rep.of (ρ.comp (C.leviEmbedding F.Carrier))) :=
    (T.isLeviSquareIntegrable_singleBlock_iff C hC ρ).mpr hsq
  obtain ⟨R, ω, t, hωirr, hωcusp, hωunit, ht, q, hq⟩ :=
    glDiscreteSeriesPositiveRootSupport p F T n hn C
      (Rep.of (ρ.comp (C.leviEmbedding F.Carrier))) hpullirr hpullsq
  refine ⟨R, ω, t, hωirr, hωcusp, hωunit, ht, ?_⟩
  let q' : Representation.IntertwiningMap
      ((RelativeJacquetMultiplicity.innerInduced T C R
        (RelativeJacquetMultiplicity.fineTwist T C R ω t 0)).ρ.comp
          e.symm.toMonoidHom) ρ :=
    { toLinearMap := q.toLinearMap
      isIntertwining' := by
        intro g
        ext v
        change q ((RelativeJacquetMultiplicity.innerInduced T C R
          (RelativeJacquetMultiplicity.fineTwist T C R ω t 0)).ρ (e.symm g) v) =
            ρ g (q v)
        have h := DFunLike.congr_fun (q.isIntertwining' (e.symm g)) v
        change q ((RelativeJacquetMultiplicity.innerInduced T C R
          (RelativeJacquetMultiplicity.fineTwist T C R ω t 0)).ρ (e.symm g) v) =
            ρ (e (e.symm g)) (q v) at h
        simpa only [e.apply_symm_apply] using h }
  exact ⟨q', hq⟩

end Langlands
