import Langlands.Automorphic.Unramified.IsobaricWeakBaseChangeTransportStatement
import Langlands.Automorphic.Unramified.IsobaricSpectralUniqueness

/-!
# Weak base change of isobaric data in a tower

For a tower of number fields `F ⊆ K ⊆ E`, arithmetic weak base change of spectral systems
from `F` to `K` and from `K` to `E` composes to arithmetic weak base change from `F` to `E`,
once the two middle systems have the same spectra at almost all places of `K`. Two systems
attached to the same isobaric data over `K` have this property, so weak base change of
isobaric data composes in the tower, with independent factor universes at the three fields.
-/

noncomputable section

universe uF uK uE uV uM uW

set_option autoImplicit false

namespace Langlands.Unramified.SpectralSystem

open IsDedekindDomain
open Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped NumberField

variable {F : Type uF} {K : Type uK} {E : Type uE} [Field F] [Field K] [Field E]
  [NumberField F] [NumberField K] [NumberField E]
  [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]

omit [NumberField F] in
/-- Arithmetic weak base change composes in a tower `F ⊆ K ⊆ E`: if `t` over `K` is a weak
base change of `s` over `F`, `u` over `E` is a weak base change of `t'` over `K`, and `t`
and `t'` have the same spectra at almost all places of `K`, then `u` is a weak base change
of `s`. -/
theorem IsArithmeticWeakBaseChangeOf.trans_of_eventually_eigenvalues_eq {n : ℕ}
    {s : SpectralSystem (FinitePlace F) n} {t t' : SpectralSystem (FinitePlace K) n}
    {u : SpectralSystem (FinitePlace E) n}
    (hts : t.IsArithmeticWeakBaseChangeOf s)
    (htt' : ∀ᶠ w in Filter.cofinite, ∀ (hw : w ∉ t.exceptional) (hw' : w ∉ t'.exceptional),
      t.eigenvalues w hw = t'.eigenvalues w hw')
    (hut' : u.IsArithmeticWeakBaseChangeOf t') :
    u.IsArithmeticWeakBaseChangeOf s := by
  classical
  have hK := Filter.eventually_cofinite.mp (htt'.and hut')
  filter_upwards [hts, eventually_avoidsAbove (F := F) hK.toFinset] with v hv hgood
  obtain ⟨hs, ht, hram, heig⟩ := hv
  have hmid : ∀ x : FinitePlacesAbove E v,
      ∃ hx : x.1 ∉ u.exceptional, x.1.asIdeal.ramificationIdx (𝓞 F) = 1 ∧
        u.eigenvalues x.1 hx = (s.eigenvalues v hs).power (x.1.asIdeal.inertiaDeg (𝓞 F)) := by
    intro x
    have hxv : x.1.asIdeal.LiesOver v.asIdeal := x.2
    let w : FinitePlacesAbove K v :=
      ⟨x.1.under (𝓞 K), Ideal.LiesOver.tower_bot x.1.asIdeal _ v.asIdeal⟩
    have hxw : x.1.asIdeal.LiesOver w.1.asIdeal := liesOver_under x.1
    have hw := hgood w
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hw
    obtain ⟨heq, hs', hu, hram', heig'⟩ := hw
    let x' : FinitePlacesAbove E w.1 := ⟨x.1, hxw⟩
    refine ⟨hu x', ?_, ?_⟩
    · rw [Ideal.ramificationIdx_tower (R := 𝓞 F) w.1.asIdeal x.1.asIdeal, hram w, hram' x',
        one_mul]
    · rw [heig' x', ← heq (ht w) hs', heig w, Eigenvalues.power_power,
        Ideal.inertiaDeg_tower (R := 𝓞 F) w.1.asIdeal x.1.asIdeal]
  choose hx hrest using hmid
  exact ⟨hs, hx, fun x => (hrest x).1, fun x => (hrest x).2⟩

omit [NumberField F] in
/-- The tower composition of arithmetic weak base change, for systems whose ranks are
identified by equalities `m = n` and `p = m`, as in `IsobaricData.IsWeakBaseChangeOf`. -/
theorem IsArithmeticWeakBaseChangeOf.trans_eqRec {n m p : ℕ} (hmn : m = n) (hpm : p = m)
    {s : SpectralSystem (FinitePlace F) n} {t t' : SpectralSystem (FinitePlace K) m}
    {u : SpectralSystem (FinitePlace E) p}
    (hts : SpectralSystem.IsArithmeticWeakBaseChangeOf (hmn ▸ t) s)
    (htt' : ∀ᶠ w in Filter.cofinite, ∀ (hw : w ∉ t.exceptional) (hw' : w ∉ t'.exceptional),
      t.eigenvalues w hw = t'.eigenvalues w hw')
    (hut' : SpectralSystem.IsArithmeticWeakBaseChangeOf (hpm ▸ u) t') :
    SpectralSystem.IsArithmeticWeakBaseChangeOf ((hpm.trans hmn) ▸ u) s := by
  subst hmn hpm
  exact hts.trans_of_eventually_eigenvalues_eq htt' hut'

end Langlands.Unramified.SpectralSystem

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Unramified

/-- **Weak base change in a tower.** For number fields `F ⊆ K ⊆ E`, a weak base change to `E`
of a weak base change to `K` of isobaric data over `F` is a weak base change to `E` of those
data. The two systems attached to the middle data may come from different presentations. -/
theorem isobaricWeakBaseChangeTower :
    IsobaricWeakBaseChangeTowerStatement.{uF, uK, uE, uV, uM, uW} := by
  intro F K E _ _ _ _ _ _ _ _ _ _ _ _ _ DF DK DE hKF hEK
  obtain ⟨hrKF, s, t, hs, ht, hts⟩ := hKF
  obtain ⟨hrEK, t', u, ht', hu, hut'⟩ := hEK
  exact ⟨hrEK.trans hrKF, s, u, hs, hu,
    SpectralSystem.IsArithmeticWeakBaseChangeOf.trans_eqRec hrKF hrEK hts
      (ht.eventually_eigenvalues_eq ht') hut'⟩

end Langlands.Automorphic.Unramified
