import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Langlands.LocalField.PadicResidueNormalization
import Langlands.Representation.RankinSelberg.TemperedTwistSupercuspidalPoleClassification

/-! # Essential square integrability in the local sigma-lift vocabulary -/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.JacquetLanglands

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Both determinants use the same residue-normalized absolute value. -/
theorem determinantNorm_eq_padic (T : F.TopologicalData) (n : ℕ) :
    let := T.topology
    let := T.valuativeRel
    have := T.localField
    determinantNorm F.Carrier n = T.determinantNorm n := by
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply NNReal.coe_injective
  simpa only [determinantNorm_coe, PadicField.TopologicalData.determinantNorm_coe] using
    T.residueNormalizedAbsoluteValue_eq_normalizedAbs (GeneralLinear.determinant g : F.Carrier)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {n : ℕ}

/-- With the supplied p-adic topology, the sigma-lift property of essential
square integrability agrees with the existing p-adic property. -/
theorem isEssentiallySquareIntegrable_iff_padic (T : F.TopologicalData)
    (π : Representation ℂ (GeneralLinear n F.Carrier) V) :
    let := T.topology
    let := T.valuativeRel
    have := T.localField
    IsEssentiallySquareIntegrable π ↔ T.IsEssentiallySquareIntegrable π := by
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  change IsEssentiallySquareIntegrable π ↔ T.IsEssentiallySquareIntegrable π
  unfold IsEssentiallySquareIntegrable PadicField.TopologicalData.IsEssentiallySquareIntegrable
  rw [determinantNorm_eq_padic T n]
  rfl

private theorem isSquareIntegrable_iff_of_topology_eq (T U : F.TopologicalData)
    (h : T.topology = U.topology) (π : Representation ℂ (GeneralLinear n F.Carrier) V) :
    T.IsSquareIntegrable π ↔ U.IsSquareIntegrable π := by
  cases T
  cases U
  cases h
  rfl

private theorem isEssentiallySquareIntegrable_iff_of_topology_eq (T U : F.TopologicalData)
    (h : T.topology = U.topology) (π : Representation ℂ (GeneralLinear n F.Carrier) V) :
    T.IsEssentiallySquareIntegrable π ↔ U.IsEssentiallySquareIntegrable π := by
  have hnorm : T.determinantNorm n = U.determinantNorm n := T.determinantNorm_eq U n
  unfold PadicField.TopologicalData.IsEssentiallySquareIntegrable
  rw [hnorm]
  exact exists_congr fun _ => isSquareIntegrable_iff_of_topology_eq T U h _

/-- Every irreducible supercuspidal action of positive rank over a p-adic
field is essentially square-integrable in the local sigma-lift vocabulary. -/
def PadicSupercuspidalEssentialSquareIntegrabilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n F.Carrier) V),
      π.IsIrreducible →
      let := T.topology
      let := T.valuativeRel
      have := T.localField
      GeneralLinear.IsSupercuspidal π → IsEssentiallySquareIntegrable π

/-- Transport the published supercuspidal result to the generic predicate
through the equal topologies and determinant characters. -/
theorem padicSupercuspidalEssentialSquareIntegrability :
    PadicSupercuspidalEssentialSquareIntegrabilityStatement.{uF, uV} := by
  intro p hp F T n hn V _ _ π hirr
  dsimp only
  intro hSC
  let U := F.canonicalTopologicalData
  have ht : T.topology = U.topology :=
    T.topology_eq_canonicalModule.trans U.topology_eq_canonicalModule.symm
  have hSC' : let := U.topology; GeneralLinear.IsSupercuspidal π :=
    (congrArg (fun t => @GeneralLinear.IsSupercuspidal F.Carrier _ t n V _ _ π) ht) ▸ hSC
  have hSQ : U.IsEssentiallySquareIntegrable π := by
    let := U.topology
    cases n with
    | zero => exact (Nat.lt_irrefl 0 hn).elim
    | succ j =>
      exact RankinSelberg.supercuspidal_isEssentiallySquareIntegrable F j
        (SmoothRep.of π hSC'.1.1) hirr hSC'
  exact (isEssentiallySquareIntegrable_iff_padic T π).mpr
    ((isEssentiallySquareIntegrable_iff_of_topology_eq T U ht π).mpr hSQ)

end Langlands.JacquetLanglands
