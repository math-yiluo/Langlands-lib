import Langlands.Correspondence.HenniartStableMapStatement
import Langlands.Correspondence.SupercuspidalFinitenessStatement
import Langlands.Correspondence.HenniartExtensionDeterminant
import Langlands.Correspondence.RankOneExistence
import Langlands.Representation.Conductor.GenericEpsilonConductor
import Langlands.Representation.RankinSelberg.SupercuspidalLFactorCharacterizationSupport
import Langlands.Representation.RankinSelberg.UnramifiedUnitaryPoleFreeProof
import Langlands.Representation.RankinSelberg.PairEpsilonNormalizationStatement

/-!
# Finiteness of Henniart's candidate sets from the conductor theorems

Henniart (2000), §4.3: a supercuspidal class of `GL_(k+1)(K)` with a prescribed
central character and a prescribed epsilon factor against the trivial character of
`GL_1(K)` lies in a finite set. The exponent `m` of `ε(s, π × 1, ψ) = c q^(-ms)`
determines the conductor `f(π) = m - (k+1) n(ψ)` (Bushnell–Henniart–Kutzko 1998),
which is the least level with nonzero fixed vectors (Jacquet–Piatetski-Shapiro–
Shalika 1981, Théorème (5.1)). Bernstein–Zelevinsky (1976), Corollary 4.15, bounds the
number of supercuspidal classes with fixed central character and bounded level.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence StableMap HarmonicAnalysis

universe uK uV

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartConductorFinitenessTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance henniartConductorFinitenessValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance henniartConductorFinitenessLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField

/-- The constructed rank-one object of the trivial character is the scalar model
`rankOneCharacter 1`, through `ULift ℂ ≃ ℂ`. -/
def trivialRankOneEquiv :
    (rankOneSupercuspidalObject.{uK, uV} K 1).obj.representation.Equiv
      (RankinSelberg.rankOneCharacter (1 : K.Carrierˣ →* ℂˣ)) where
  toLinearEquiv := ULift.moduleEquiv
  isIntertwining' g := by
    ext v
    change ((1 : ℂˣ) : ℂ) • v.down = (1 : ℂ) • v.down
    simp

/-- Bushnell–Henniart–Kutzko and JPSS (5.1): if `c q^(-ms)` is the epsilon factor of a
supercuspidal `π` of `GL_(k+1)(K)` against the trivial character of `GL_1(K)`, for
`ψ` and a measure self-dual for `ψ`, then `m - (k+1) n(ψ)` is a natural number `b`
and `b` is the least level with nonzero fixed vectors. -/
theorem exists_newvectorConductor_of_pairEpsilon
    (hBHK : RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0})
    (hJPSS : Conductor.ConductorExponentStatement.{uK, uV})
    (ψ : NontrivialAdditiveCharacter K) (ν : LocalAdditiveHaarMeasure K)
    (hν : IsSelfDualMeasure K ψ ν) {k : ℕ}
    (A : GeneralLinear.SupercuspidalRep.{uK, uV} (F := K.Carrier) (n := k + 1))
    {c : ℂˣ} {m : ℤ}
    (h : RankinSelberg.IsPadicSymmetricEpsilonFactor K ψ ν A.obj.representation
      (rankOneSupercuspidalObject.{uK, uV} K 1).obj.representation (c, m)) :
    ∃ b : ℕ, (b : ℤ) = m - ((k + 1 : ℕ) : ℤ) * K.canonicalTopologicalData.additiveConductor ψ ∧
      Conductor.IsNewvectorConductor A.obj.representation b := by
  have h' : RankinSelberg.IsPadicPairEpsilonFactor K ψ ν A.obj.representation
      (RankinSelberg.rankOneCharacter (1 : K.Carrierˣ →* ℂˣ)) (c, m) :=
    (RankinSelberg.isPadicSymmetricEpsilonFactor_of_le (Nat.zero_le k)).mp
      ((RankinSelberg.IsPadicSymmetricEpsilonFactor.congr_equiv
        (Representation.Equiv.refl _) (trivialRankOneEquiv K)).mp h)
  have hA : Whittaker.IsGeneric (ψ : UnitaryAdditiveCharacter K.Carrier) k
      A.obj.representation :=
    RankinSelberg.SupercuspidalLFactorCharacterization.isGeneric_of_isSupercuspidal K ψ k
      A.obj A.property.1 A.property.2
  obtain ⟨a, hψ₀⟩ := RankinSelberg.UnramifiedUnitary.exists_scale_hasIntegerConductor K ψ
  have hA₀ : Whittaker.IsGeneric ((ψ : UnitaryAdditiveCharacter K.Carrier).scale a) k
      A.obj.representation :=
    RankinSelberg.SupercuspidalLFactorCharacterization.isGeneric_of_isSupercuspidal K _ k
      A.obj A.property.1 A.property.2
  have hψeq := Conductor.genericConductor_eq K ψ A.obj.representation hA ν hν h'
  have hind : Conductor.genericConductor K ψ A.obj.representation hA =
      Conductor.genericConductor K ((ψ : UnitaryAdditiveCharacter K.Carrier).scale a)
        A.obj.representation hA₀ :=
    Conductor.genericPairConductor_eq_of_pairEpsilonExponentStatement K hBHK
      A.obj.representation (RankinSelberg.rankOneCharacter (1 : K.Carrierˣ →* ℂˣ)) _ _ hA
      (RankinSelberg.UniformRankOneTwist.isGeneric_rankOneCharacter_one K _) hA₀
      (RankinSelberg.UniformRankOneTwist.isGeneric_rankOneCharacter_one K _)
  obtain ⟨b, hb, hnew, -⟩ :=
    Conductor.genericConductor_isNewvectorConductor_of_conductorExponentStatement K hJPSS
      _ hψ₀ A.obj.representation hA₀
  exact ⟨b, by rw [← hb, ← hind, hψeq], hnew⟩

/-- Henniart (2000), §4.3: the finiteness of the candidate sets, from
Bernstein–Zelevinsky's bounded-level finiteness, Bushnell–Henniart–Kutzko's
dependence of the epsilon exponent on `ψ`, and JPSS (5.1). -/
theorem supercuspidalEpsilonConductorFiniteness_of_conductor
    (hBZ : SupercuspidalBoundedLevelFinitenessStatement.{uK, uV})
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
  refine (hBZ K.Carrier k χ b).subset ?_
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
Bernstein–Zelevinsky's bounded-level finiteness, Bushnell–Henniart–Kutzko's
dependence of the epsilon exponent on `ψ`, and JPSS (5.1). -/
def SupercuspidalEpsilonConductorFinitenessReductionStatement : Prop :=
  SupercuspidalBoundedLevelFinitenessStatement.{uK, uV} →
  RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0} →
  Conductor.ConductorExponentStatement.{uK, uV} →
  SupercuspidalEpsilonConductorFinitenessStatement.{uK, uV}

theorem supercuspidalEpsilonConductorFinitenessReduction :
    SupercuspidalEpsilonConductorFinitenessReductionStatement.{uK, uV} :=
  fun hBZ hBHK hJPSS => supercuspidalEpsilonConductorFiniteness_of_conductor hBZ hBHK hJPSS

end Langlands.Henniart.Extension
