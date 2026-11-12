import Langlands.Correspondence.HenniartConductorFinitenessProof
import Langlands.Correspondence.PadicSupercuspidalFinitenessProof

/-!
# Finiteness of Henniart's candidate sets with p-adic Bernstein–Zelevinsky finiteness

`supercuspidalEpsilonConductorFiniteness_of_conductor` derives the finiteness of
Henniart's candidate sets (Henniart (2000), §4.3) from bounded-level finiteness of
supercuspidal classes over every nonarchimedean local field, together with the
Bushnell–Henniart–Kutzko and JPSS conductor theorems. The candidate sets only involve
p-adic fields, and `CompactOpenFiniteness.centralLevelStratum_finite` proves
bounded-level finiteness over them, so that hypothesis is dropped here.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence StableMap HarmonicAnalysis

universe uK uV

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartPadicConductorTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance henniartPadicConductorValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance henniartPadicConductorLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField

/-- Henniart (2000), §4.3: the finiteness of the candidate sets, from
Bushnell–Henniart–Kutzko's dependence of the epsilon exponent on `ψ` and JPSS (5.1);
Bernstein–Zelevinsky's bounded-level finiteness over p-adic fields is
`CompactOpenFiniteness.centralLevelStratum_finite`. -/
theorem supercuspidalEpsilonConductorFiniteness_of_pairEpsilon
    (hBHK : RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0})
    (hJPSS : Conductor.ConductorExponentStatement.{uK, uV}) :
    SupercuspidalEpsilonConductorFinitenessStatement.{uK, uV} := by
  intro p _ K ψ ν hν k ω m
  have hbij : Function.Bijective
      (GeneralLinear.scalarToCenter : K.Carrierˣ →*
        Subgroup.center (GeneralLinear (k + 1) K.Carrier)) := by
    constructor
    · intro a b hab
      exact (GeneralLinear.scalarEmbedding (Nat.succ_pos k)).injective
        (congrArg Subtype.val hab)
    · intro z
      have hz := z.property
      simp only [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
      obtain ⟨a, ha⟩ := hz
      exact ⟨a, Subtype.ext ha⟩
  let e : K.Carrierˣ ≃* Subgroup.center (GeneralLinear (k + 1) K.Carrier) :=
    MulEquiv.ofBijective GeneralLinear.scalarToCenter hbij
  let χ : Subgroup.center (GeneralLinear (k + 1) K.Carrier) →* ℂˣ :=
    ω.comp e.symm.toMonoidHom
  let b : ℕ := (m - ((k + 1 : ℕ) : ℤ) * K.canonicalTopologicalData.additiveConductor ψ).toNat
  refine (CompactOpenFiniteness.centralLevelStratum_finite.{uK, uV} K k χ b).subset ?_
  rintro π ⟨hω, c, hε⟩
  obtain ⟨A, rfl⟩ := Quotient.exists_rep π
  obtain ⟨b', hb', hnew⟩ := exists_newvectorConductor_of_pairEpsilon K hBHK hJPSS ψ ν hν A hε
  have hbb : b = b' := by
    change (m - _).toNat = b'
    rw [← hb']
    exact Int.toNat_natCast b'
  refine ⟨?_, ?_⟩
  · intro z v
    obtain ⟨a, rfl⟩ := e.surjective z
    change A.obj.representation (GeneralLinear.scalar a) v = (ω (e.symm (e a)) : ℂ) • v
    rw [e.symm_apply_apply]
    exact (supercuspidalCentralActsBy_iff K (n := k.succPNat) A a (ω a)).mp (hω a) v
  · change Conductor.firstFixedLevel A.obj.representation ≤ (b : WithTop ℕ)
    rw [Conductor.firstFixedLevel_le_iff, hbb]
    exact hnew.1

/-- Henniart (2000), §4.3: the finiteness of the candidate sets follows from
Bushnell–Henniart–Kutzko's dependence of the epsilon exponent on `ψ` and JPSS (5.1)
alone, Bernstein–Zelevinsky's finiteness being proved over p-adic fields. -/
def SupercuspidalEpsilonConductorFinitenessPadicReductionStatement : Prop :=
  RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0} →
  Conductor.ConductorExponentStatement.{uK, uV} →
  SupercuspidalEpsilonConductorFinitenessStatement.{uK, uV}

/-- Proof of `SupercuspidalEpsilonConductorFinitenessPadicReductionStatement`. -/
theorem supercuspidalEpsilonConductorFinitenessPadicReduction :
    SupercuspidalEpsilonConductorFinitenessPadicReductionStatement.{uK, uV} :=
  fun hBHK hJPSS => supercuspidalEpsilonConductorFiniteness_of_pairEpsilon hBHK hJPSS

end Langlands.Henniart.Extension
