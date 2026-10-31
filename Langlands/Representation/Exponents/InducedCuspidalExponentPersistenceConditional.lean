import Langlands.Representation.Exponents.InducedCuspidalExponentPersistenceStatement
import Langlands.Representation.Exponents.CuspidalInductionJacquetConstituentConditional
import Langlands.Representation.Exponents.PersistenceTransport
import Langlands.Representation.Exponents.InnerCuspidalUpperSupport
import Langlands.Representation.Jacquet.RefinedRealTwistEquiv
import Langlands.Representation.Geometric.InducedOppositePersistentPieceConditional

/-! Persistence assembly from geometric-lemma and cuspidal-constituent inputs. -/

noncomputable section

namespace Langlands.InducedCuspidalExponentPersistence

open GeneralLinear Geometric CuspidalSupport RelativeJacquetMultiplicity
open RealTwistFamilies WeylBranchPieces

universe uF uV uW uM

/-- The same geometric filtration index yields both the parameter-t
identification and occurrence at zero. The final proof supplies both premises
from the published geometric lemma. -/
theorem persistence_of_geometricLemma_of_constituent
    (hgeo : PadicGeometricLemmaTheorem.{uF, uW})
    (hC : GLCuspidalInductionJacquetConstituentStatement.{uF, uV, uM}) :
    GLInducedCuspidalExponentPersistenceStatement.{uF, uV, uW, uM} := by
  intro p _ F T
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  intro n hn B S ω hωi hωc v π _ hq t E τ hτc hτ
  have hπs : IsSmooth π.ρ := by
    obtain ⟨q, hq⟩ := hq
    exact isSmooth_of_surjective q hq
      (T.isSmooth_normalizedRefinedInduced B S (fineTwist T B S ω v 0).ρ)
  let πt := Rep.of (T.leviRealPowerTwist B t π.ρ)
  have hπts : IsSmooth πt.ρ := (T.isSmooth_leviRealPowerTwist_iff B t π.ρ).mpr hπs
  obtain ⟨R, w, hw, hsubt, hpersist⟩ :=
    InducedOppositeCuspidalPiece.persistentCuspidalPiece_of_geometricLemma T B E hn
      (hgeo p F T n hn B E.reverse) πt hπts τ hτ.1 hτc hτ.2.2
  let ρt := transport E (B.flatten R) w⁻¹ (conjugatesLevi_inv hw) τ.ρ
  have hρti : Representation.IsIrreducible ρt :=
    (isIrreducible_transport w⁻¹ (conjugatesLevi_inv hw) τ.ρ).mpr hτ.1
  have hρtc : IsLeviCuspidal (B.flatten R) ρt :=
    isLeviCuspidal_transport_of_conjugatesLevi E (B.flatten R) w⁻¹
      (conjugatesLevi_inv hw) τ.ρ hτc
  have hsubt' : IsSubquotient
      ((T.normalizedRefinedJacquet B R πt.ρ).comp
        (flattenedLeviEquiv F.Carrier B R).toMonoidHom) ρt := by
    change IsSubquotient _ (transport E (B.flatten R) w⁻¹
      (conjugatesLevi_inv hw) τ.ρ)
    rw [transport_inv hw]
    exact IsSubquotient.of_comp_symm
      (leviConjugation (B.flatten R) E w hw) hsubt
  let ρ := Rep.of (T.leviRealPowerTwist (B.flatten R) (-(restrictParameter B R t)) ρt)
  have hρi : Representation.IsIrreducible ρ.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff (B.flatten R) _ ρt).mpr hρti
  have hρc : IsLeviCuspidal (B.flatten R) ρ.ρ :=
    (T.isLeviCuspidal_leviRealPowerTwist_iff (B.flatten R) _ ρt).mpr hρtc
  have hsub0 : IsSubquotient
      ((T.normalizedRefinedJacquet B R π.ρ).comp
        (flattenedLeviEquiv F.Carrier B R).toMonoidHom) ρ.ρ := by
    have h := (IsSubquotient.of_equiv_left
      (T.flattenedNormalizedRefinedJacquetRealTwistEquiv B R t π.ρ).symm hsubt').twist
        (T.leviRealPowerCharacter (B.flatten R) (-(restrictParameter B R t)))
    change IsSubquotient
      (T.leviRealPowerTwist (B.flatten R) (-(restrictParameter B R t))
        (T.leviRealPowerTwist (B.flatten R) (restrictParameter B R t)
          ((T.normalizedRefinedJacquet B R π.ρ).comp
            (flattenedLeviEquiv F.Carrier B R).toMonoidHom))) ρ.ρ at h
    rwa [T.leviRealPowerTwist_neg_cancel] at h
  obtain ⟨h, hh, hc, ⟨e0⟩⟩ :=
    InnerCuspidalQuotientSupport.exists_transport_fineTwist_of_upper_quotient_of_constituent
      T B R hC hn S ω hωi v π ρ hρi hωc hρc hq hsub0
  have hcancel : T.leviRealPowerTwist (B.flatten R) (restrictParameter B R t) ρ.ρ =
      ρt := T.leviRealPowerTwist_cancel_neg (B.flatten R) (restrictParameter B R t) ρt
  have et : (transport (B.flatten S) (B.flatten R) h hc
      (T.leviRealPowerTwist (B.flatten S) (nestedParameter B S v t) ω.ρ)).Equiv ρt := by
    rw [T.transport_nestedLeviRealPowerTwist B S R h hh hc]
    have e := twistEquiv (T.leviRealPowerCharacter (B.flatten R) (restrictParameter B R t)) e0
    change (T.leviRealPowerTwist (B.flatten R) (restrictParameter B R t) ρ.ρ).Equiv
      (T.leviRealPowerTwist (B.flatten R) (restrictParameter B R t)
        (transport (B.flatten S) (B.flatten R) h hc
          (T.leviRealPowerTwist (B.flatten S) (-v) ω.ρ))) at e
    rw [hcancel] at e
    exact e.symm
  have hreturn : transport (B.flatten R) E w hw ρt = τ.ρ := by
    change transport (B.flatten R) E w hw
      (transport E (B.flatten R) w⁻¹ (conjugatesLevi_inv hw) τ.ρ) = τ.ρ
    rw [transport_transport (conjugatesLevi_inv hw) hw
      (CuspidalSupport.conjugatesLevi_one E) (mul_inv_cancel w), transport_one]
  let hs := conjugatesLevi_mul hc hw
  refine ⟨w * h, hs, ?_, ?_⟩
  · have e := transportEquiv w hw et
    rw [← transport_mul hc hw, hreturn] at e
    exact ⟨e⟩
  · have hinner0 : IsSubquotient
        ((T.normalizedRefinedJacquet B R π.ρ).comp
          (flattenedLeviEquiv F.Carrier B R).toMonoidHom)
        (transport (B.flatten S) (B.flatten R) h hc
          (T.leviRealPowerTwist (B.flatten S) (-v) ω.ρ)) :=
      hsub0.of_equiv_right e0
    have hpiece0 := hinner0.comp (leviConjugation (B.flatten R) E w hw).symm.toMonoidHom
    change IsSubquotient
      (transport (B.flatten R) E w hw
        ((T.normalizedRefinedJacquet B R π.ρ).comp
          (flattenedLeviEquiv F.Carrier B R).toMonoidHom))
      (transport (B.flatten R) E w hw
        (transport (B.flatten S) (B.flatten R) h hc
          (T.leviRealPowerTwist (B.flatten S) (-v) ω.ρ))) at hpiece0
    rw [← transport_mul hc hw] at hpiece0
    have hsub := (hpersist π hπs).trans hpiece0
    have hzero : T.IsOppositeJacquetClassExponent E
        (CuspidalJacquetMultiplicity.induced T B π)
        (Rep.of (transport (B.flatten S) E (w * h) hs
          (T.leviRealPowerTwist (B.flatten S) (-v) ω.ρ))) :=
      ⟨(isIrreducible_transport (w * h) hs _).mpr
          ((T.isIrreducible_leviRealPowerTwist_iff (B.flatten S) (-v) ω.ρ).mpr hωi),
        isAdmissible_transport (w * h) hs
          ((T.isAdmissible_leviRealPowerTwist_iff (B.flatten S) (-v) ω.ρ).mpr hωc.1),
        hsub⟩
    simpa only [Occurs, induced_zero, transported, nestedParameter_zero] using hzero

/-- The published tensor constituent reduction and the cuspidal-piece extraction
reduce both required inputs to geometric-lemma instances. The fine and coarse
representation universes remain independent. -/
theorem persistence_of_geometricLemmas
    (hgeoCoarse : PadicGeometricLemmaTheorem.{uF, uW})
    (hgeoFine : PadicGeometricLemmaTheorem.{uF, uV}) :
    GLInducedCuspidalExponentPersistenceStatement.{uF, uV, uW, uM} := by
  exact persistence_of_geometricLemma_of_constituent hgeoCoarse
    (Langlands.glCuspidalInductionJacquetConstituent_of_cuspidalPiece.{uF, uV, uM}
      (InducedOppositeCuspidalPiece.glInducedOppositeJacquetCuspidalPiece_of_padicGeometricLemma.{uF, uM, uV}
        hgeoFine))

end Langlands.InducedCuspidalExponentPersistence
