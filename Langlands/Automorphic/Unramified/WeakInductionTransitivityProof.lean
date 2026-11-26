import Langlands.Automorphic.Unramified.WeakInductionTransitivityStatement
import Langlands.Global.Arithmetic.HarrisProposition48PrimeInductionStagesProof

/-! # Transitivity of arithmetic weak induction in towers: proof -/

noncomputable section

universe uF uK uE uV uM uW uM'

set_option autoImplicit false

namespace Langlands.Unramified.SpectralSystem

open IsDedekindDomain Polynomial
open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic.Unramified.WeakInduction
open scoped NumberField

variable {F : Type uF} {K : Type uK} {E : Type uE}
  [Field F] [NumberField F] [Field K] [NumberField K] [Field E] [NumberField E]
  [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]

/-- **Arithmetic weak induction in stages.** For a tower `E/K/F`, if `s` over `F` is an
arithmetic weak induction of `t` over `K` and `t` is one of `u` over `E`, then `s` is an
arithmetic weak induction of `u`. -/
theorem IsArithmeticWeakInductionOf.trans_tower {n m l : ℕ}
    {s : SpectralSystem (FinitePlace F) n} {t : SpectralSystem (FinitePlace K) m}
    {u : SpectralSystem (FinitePlace E) l}
    (hst : s.IsArithmeticWeakInductionOf t) (htu : t.IsArithmeticWeakInductionOf u) :
    s.IsArithmeticWeakInductionOf u := by
  classical
  refine ⟨?_, ?_⟩
  · rw [hst.1, htu.1, Nat.mul_assoc, Nat.mul_comm (Module.finrank K E),
      Module.finrank_mul_finrank]
  filter_upwards [hst.2, eventually_forall_finitePlacesAbove (K := F) htu.2] with v hv hw
  obtain ⟨hs, ht, hram, heul⟩ := hv
  let e := finitePlacesAboveTower (K := F) (E := K) (M := E) v
  have hu : ∀ z : FinitePlacesAbove E v, z.1 ∉ u.exceptional := by
    intro z
    obtain ⟨_, hu', _, _⟩ := hw (e.symm z).1
    exact hu' (e.symm z).2
  refine ⟨hs, hu, fun z => ?_, ?_⟩
  · let p := e.symm z
    obtain ⟨_, _, hram', _⟩ := hw p.1
    have : z.1.asIdeal.LiesOver p.1.1.asIdeal := p.2.2
    rw [Ideal.ramificationIdx_tower (R := 𝓞 F) p.1.1.asIdeal z.1.asIdeal, hram p.1, one_mul]
    exact hram' p.2
  · rw [heul, inducedEulerPolynomial, inducedEulerPolynomial]
    symm
    rw [← Fintype.prod_equiv e _ _ (fun _ => rfl), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun w _ => ?_
    obtain ⟨_, hu', _, heul'⟩ := hw w
    rw [heul', inducedEulerPolynomial, Polynomial.prod_comp]
    refine Finset.prod_congr rfl fun z _ => ?_
    have : z.1.asIdeal.LiesOver w.1.asIdeal := z.2
    have : z.1.asIdeal.LiesOver v.asIdeal :=
      Ideal.LiesOver.trans z.1.asIdeal w.1.asIdeal v.asIdeal
    change (u.eulerPolynomial z.1 _).comp (X ^ z.1.asIdeal.inertiaDeg (𝓞 F)) =
      ((u.eulerPolynomial z.1 _).comp (X ^ z.1.asIdeal.inertiaDeg (𝓞 K))).comp
        (X ^ w.1.asIdeal.inertiaDeg (𝓞 F))
    rw [Polynomial.comp_assoc, X_pow_comp, ← pow_mul,
      Ideal.inertiaDeg_tower (R := 𝓞 F) w.1.asIdeal z.1.asIdeal, Nat.mul_comm]

end Langlands.Unramified.SpectralSystem

namespace Langlands.Automorphic.CuspidalOperatorRealization.IsoClass

open Langlands.Global Langlands.Unramified

variable {F : Type uF} {K : Type uK} {E : Type uE}
  [Field F] [NumberField F] [Field K] [NumberField K] [Field E] [NumberField E]
  [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
  [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient K)]
  [CompactSpace (AdeleQuotient E)]

/-- **Weak induction of cuspidal classes in stages.** For a tower `E/K/F`, weak induction
of `c` from `b` and of `b` from `d` gives weak induction of `c` from `d`. The two spectral
systems of the middle class `b` may come from different presentations, in different
universes. -/
theorem IsWeakInductionOf.trans_tower {r s m : ℕ}
    {c : IsoClass F r} {b : IsoClass K s} {d : IsoClass E m}
    (hcb : IsWeakInductionOf.{uF, uK, uV, uM} c b)
    (hbd : IsWeakInductionOf.{uK, uE, uM', uW} b d) :
    IsWeakInductionOf.{uF, uE, uV, uW} c d := by
  obtain ⟨sc, tb, hsc, htb, h₁⟩ := hcb
  obtain ⟨tb', ud, htb', hud, h₂⟩ := hbd
  have h₂' : tb.IsArithmeticWeakInductionOf ud :=
    h₂.of_sameEulerPolynomials (htb'.sameEulerPolynomials htb)
      (SpectralSystem.sameEulerPolynomials_refl ud)
  exact ⟨sc, ud, hsc, hud, h₁.trans_tower h₂'⟩

end Langlands.Automorphic.CuspidalOperatorRealization.IsoClass

namespace Langlands.Automorphic.Unramified

/-- Arithmetic weak induction of actual cuspidal classes is transitive in towers of
number fields. -/
theorem weakInductionTransitivity :
    WeakInductionTransitivityStatement.{uF, uK, uE, uV, uM, uW} := by
  intro F K E _ _ _ _ _ _ _ _ _ _ _ _ _ r s m c b d hcb hbd
  exact hcb.trans_tower hbd

end Langlands.Automorphic.Unramified
