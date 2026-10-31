import Langlands.Representation.Classification.RelativeJacquetFiltrationMultiplicityProof
import Langlands.Representation.Classification.RelativeGenericJacquetTotalsStatement
import Langlands.Representation.Classification.ProductLeviCuspidalJacquetMultiplicityProof
import Langlands.Representation.Classification.CuspidalJacquetMultiplicityProof
import Langlands.Representation.Classification.FineTwistRegularityProof
import Langlands.Representation.Classification.RelativeGenericWeylCountProof
import Langlands.Representation.Parabolic.RefinementInductionTransitivityProof
import Langlands.Representation.Parabolic.ComposedFlattenedInductionProof
import Langlands.Representation.Parabolic.FlattenedOppositeJacquetComparisonProof
import Langlands.Representation.Filtration.MultiplicityTransportProof

/-! Equal actual Jacquet totals for generic fine cuspidal induction. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity CategoryTheory
  RelativeJacquetFiltrationMultiplicityProof

universe uF uV

/-- For relatively generic fine cuspidal data, both actual full opposite-Jacquet
modules of the full inner induction have finite composition series in which the
fine twist has multiplicity equal to the self-association cardinality. -/
theorem glRelativeGenericJacquetTotals :
    GLRelativeGenericJacquetTotalsStatement.{uF, uV} := by
  have hL : ProductLeviCuspidalJacquetMultiplicityStatement.{uF, uV, uV} :=
    productLeviCuspidalJacquetMultiplicity.{uF, uV, uV}
  have hG : GLCuspidalJacquetMultiplicityStatement.{uF, uV, uV} :=
    glCuspidalJacquetMultiplicityPrerequisites.{uF, uV, uV}
  intro p hp F T
  let := T.topology
  intro n hn B S ω hωirr hωcusp hωun v₀ t hgen C σ τ I N
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  have hreg := fineTwistIrreducibleAdmissible p F T n B S ω hωirr hωcusp v₀ t
  have hσirr : Representation.IsIrreducible σ :=
    (T.isIrreducible_leviRealPowerTwist_iff C _ ω.ρ).mpr hωirr
  have hσcusp : CuspidalSupport.IsLeviCuspidal C σ := hreg.2.2
  have hcard := (glRelativeGenericWeylCount p F T n hn B S ω ω.ρ
    hωirr hωcusp.1 hωun v₀ t hgen).2
  have hin : HasJordanHolderMultiplicity (innerJacquet T B S I) τ N :=
    ((hL p F T n hn B S ω σ hσirr hσcusp).2 ω σ hσirr N).mpr hcard.symm
  refine ⟨hin, ?_⟩
  let e := flattenedLeviEquiv F.Carrier B S
  let O := CuspidalJacquetMultiplicity.induced T B I
  let K := CuspidalJacquetMultiplicity.induced T C (Rep.of σ)
  have hcomp : τ.ρ.comp e.toMonoidHom = σ := by
    apply MonoidHom.ext
    intro m
    change σ (e.symm (e m)) = σ m
    rw [e.symm_apply_apply]
  let A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S) :=
    SmoothRep.of τ.ρ hreg.2.1.1
  let E := (Parabolic.normalizedRefinementInductionTransitivity.{uF, uV} F T B S).choose
  let E₁ : O.ρ.Equiv (T.normalizedComposedInduced B S τ.ρ) := by
    have E' := SmoothRep.equivOfIso (E.app A)
    dsimp only [CategoryTheory.Functor.comp_obj,
      PadicField.TopologicalData.normalizedRefinedInductionFunctor,
      normalizedRefinedInductionFunctorOf,
      PadicField.TopologicalData.normalizedParabolicInductionFunctor,
      BlockShape.normalizedInductionFunctorOf,
      PadicField.TopologicalData.normalizedComposedInductionFunctor,
      PadicField.TopologicalData.normalizedRefinedInduced,
      PadicField.TopologicalData.normalizedParabolicInduced,
      SmoothRep.representation, SmoothRep.of, Rep.of, A, O,
      CuspidalJacquetMultiplicity.induced, I, innerInduced] at E' ⊢
    exact E'
  have E₂ := (Parabolic.composedFlattenedInduction.{uF, uV} p F T n B S _ τ.ρ).choose
  have Eouter : O.ρ.Equiv K.ρ := by
    have h := E₁.trans E₂
    change Representation.Equiv O.ρ
      (T.normalizedParabolicInduced C (τ.ρ.comp e.toMonoidHom)) at h
    rw [hcomp] at h
    exact h
  let Eo := composedOppositeJacquetCongr T B S Eouter
  obtain ⟨Ef, _⟩ :=
    Parabolic.flattenedOppositeJacquetComparison.{uF, uF, max uF uV}.2 p F T n B S K
  let Ec : Representation.Equiv
      ((ambientJacquet T B S I).ρ.comp e.toMonoidHom)
      (CuspidalJacquetMultiplicity.oppositeJacquet T C K).ρ :=
    (MultiplicityTransportProof.pullEquiv e
      (ambientJacquet T B S I).ρ Eo).trans Ef
  let Et : Representation.Equiv (τ.ρ.comp e.toMonoidHom) σ := by
    rw [hcomp]
    exact Representation.Equiv.refl _
  have hstd : HasJordanHolderMultiplicity
      (CuspidalJacquetMultiplicity.oppositeJacquet T C K) (Rep.of σ) N :=
    (((hG p F T n hn C C ω σ hσirr hσcusp
      (CuspidalSupport.LevisAssociated.refl C)).2.2 ω σ hσirr N).2).mpr rfl
  have hpull : HasJordanHolderMultiplicity
      (Rep.of ((ambientJacquet T B S I).ρ.comp e.toMonoidHom))
      (Rep.of (τ.ρ.comp e.toMonoidHom)) N :=
    (equivJordanHolderMultiplicityTransport ℂ (C.Levi F.Carrier)
      (Rep.of ((ambientJacquet T B S I).ρ.comp e.toMonoidHom))
      (CuspidalJacquetMultiplicity.oppositeJacquet T C K)
      (Rep.of (τ.ρ.comp e.toMonoidHom)) (Rep.of σ) Ec Et N).mpr hstd
  exact (groupEquivJordanHolderMultiplicityTransport ℂ
    (refinedLevi F.Carrier B S) (C.Levi F.Carrier) e
    (ambientJacquet T B S I) τ N).mpr hpull

end Langlands
