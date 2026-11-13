import Langlands.Correspondence.HenniartNumericalStatement

/-!
# Henniart's numerical correspondence: the counting reduction

Equal finite counts of unramified-twist orbits of each rank and conductor, together
with finiteness of every supercuspidal conductor, make every numerical injection
surjective. This proves `NumericalOrbitReductionStatement`.
-/

noncomputable section

namespace Langlands.Henniart

universe uK uW uV

namespace Numerical

open Langlands.Correspondence Langlands.VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- Two Weil classes of rank `k + 1` lie in the same unramified-twist orbit exactly
when an unramified twist carries the second to the first. -/
theorem weilOrbitClass_eq_iff {k : ℕ} (σ τ : IrreducibleWeilClass.{uK, uW} K k.succPNat) :
    Weil.unramifiedOrbitClass (Weil.Local.localDegree K) ⟨k.succPNat, σ⟩ =
        Weil.unramifiedOrbitClass (Weil.Local.localDegree K) ⟨k.succPNat, τ⟩ ↔
      ∃ z : ℂˣ, weilUnramifiedTwist K k z τ = σ := by
  rw [Weil.unramifiedOrbitClass_eq_iff]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, eq_of_heq (Sigma.mk.inj_iff.mp hz).2⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [← hz]; rfl⟩

/-- Two supercuspidal classes of `GL_(k+1)` lie in the same unramified-twist orbit
exactly when an unramified twist carries the second to the first. -/
theorem supercuspidalOrbitClass_eq_iff {k : ℕ}
    (π ρ : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) :
    PadicSupercuspidal.unramifiedOrbitClass K ⟨k.succPNat, π⟩ =
        PadicSupercuspidal.unramifiedOrbitClass K ⟨k.succPNat, ρ⟩ ↔
      ∃ z : ℂˣ, supercuspidalUnramifiedTwist K k z ρ = π := by
  rw [PadicSupercuspidal.unramifiedOrbitClass_eq_iff]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, eq_of_heq (Sigma.mk.inj_iff.mp hz).2⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [← hz]; rfl⟩

end Numerical

open Numerical Correspondence VirtualRepresentation

/-- The finite orbit counts and finiteness of every supercuspidal conductor imply
Henniart's numerical surjectivity. -/
theorem numericalOrbitReduction : NumericalOrbitReductionStatement.{uK, uW, uV} := by
  intro hcount hfin p _ K k φ hφ π
  obtain ⟨hinj, hcond, htwist⟩ := hφ
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (hfin p K k π)
  obtain ⟨-, hB, hcard⟩ := hcount p K k a
  let so : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat →
      PadicSupercuspidal.UnramifiedOrbitClasses.{uK, uV} K :=
    fun ρ => PadicSupercuspidal.unramifiedOrbitClass K ⟨k.succPNat, ρ⟩
  let pick : ∀ c ∈ weilOrbitStratum.{uK, uW} K k a, IrreducibleWeilClass.{uK, uW} K k.succPNat :=
    fun c hc => Classical.choose hc
  have hpick : ∀ c (hc : c ∈ weilOrbitStratum.{uK, uW} K k a),
      Weil.unramifiedOrbitClass (Weil.Local.localDegree K) ⟨k.succPNat, pick c hc⟩ = c ∧
        HasArtinConductor K (pick c hc) a :=
    fun c hc => Classical.choose_spec hc
  let f : ∀ c ∈ weilOrbitStratum.{uK, uW} K k a,
      PadicSupercuspidal.UnramifiedOrbitClasses.{uK, uV} K :=
    fun c hc => so (φ (pick c hc))
  have hf : ∀ c hc, f c hc ∈ supercuspidalOrbitStratum.{uK, uV} K k a :=
    fun c hc => ⟨φ (pick c hc), rfl, hcond _ _ (hpick c hc).2⟩
  have hfinj : ∀ c₁ c₂ hc₁ hc₂, f c₁ hc₁ = f c₂ hc₂ → c₁ = c₂ := by
    intro c₁ c₂ hc₁ hc₂ h
    obtain ⟨z, hz⟩ := (supercuspidalOrbitClass_eq_iff K _ _).mp h
    rw [← htwist] at hz
    exact (hpick c₁ hc₁).1.symm.trans
      (((weilOrbitClass_eq_iff K _ _).mpr ⟨z, hinj hz⟩).trans (hpick c₂ hc₂).1)
  have hπ : so π ∈ supercuspidalOrbitStratum.{uK, uV} K k a := ⟨π, rfl, ha.symm⟩
  obtain ⟨c, hc, hcπ⟩ := Set.surj_on_of_inj_on_of_ncard_le f hf hfinj hcard.ge hB (so π) hπ
  obtain ⟨z, hz⟩ := (supercuspidalOrbitClass_eq_iff K _ _).mp hcπ
  exact ⟨weilUnramifiedTwist K k z (pick c hc), by rw [htwist, hz]⟩

end Langlands.Henniart
