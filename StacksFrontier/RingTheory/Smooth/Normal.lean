module

public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE

import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# A smooth algebra over a normal ring is normal

Proof of `Algebra.isNormalRing_of_smooth` (Stacks 033C): if `R → S` is a smooth ring map and `R`
is a normal ring, then `S` is a normal ring.

Normality is local on `S`, and locally on `S` a smooth algebra is standard étale over a polynomial
ring: every prime `q` of `S` has an `f ∉ q` with `S_f` standard étale over `R[x₁, …, xₙ]`
(`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`). The polynomial ring is normal
(Lemma 00H1, `isNormalRing_mvPolynomial`), an étale algebra over a normal ring is normal
(`IsNormalRing.of_etale`), and `S_q` is a localization of `S_f`.

## Main results

* `IsNormalRing.of_forall_exists_away`: normality of `S` is detected on basic opens around each
  prime.
* `Algebra.isNormalRing_of_smooth`: a smooth algebra over a normal ring is normal.

## Implementation notes

The ring map is an `Algebra R S` instance and its smoothness is `Algebra.Smooth R S`, as for the
reduced analogue `Algebra.isReduced_of_smooth` (Stacks 033B). Normality is the library's
`IsNormalRing` (Definition 00GV): every localization at a prime is an integrally closed domain, so
a normal ring need not be a domain.

## References

* [Stacks Project, Tag 033C](https://stacks.math.columbia.edu/tag/033C)
-/

@[expose] public section

/-- Normality is local on the spectrum: if every prime `q` of `S` has an `f ∉ q` with `S_f`
normal, then `S` is normal, the localization `S_q` being a localization of `S_f`. -/
theorem IsNormalRing.of_forall_exists_away {S : Type*} [CommRing S]
    (H : ∀ (q : Ideal S) [q.IsPrime], ∃ f ∉ q, IsNormalRing (Localization.Away f)) :
    IsNormalRing S := by
  intro q hq
  obtain ⟨f, hf, hT⟩ := H q
  have hle : Submonoid.powers f ≤ q.primeCompl := Submonoid.powers_le.mpr hf
  let _ : Algebra (Localization.Away f) (Localization.AtPrime q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ q.primeCompl hle
  have : IsScalarTower S (Localization.Away f) (Localization.AtPrime q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ q.primeCompl hle
  have : IsLocalization (q.primeCompl.map (algebraMap S (Localization.Away f)))
      (Localization.AtPrime q) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ q.primeCompl hle
  exact (hT.isLocalization (q.primeCompl.map (algebraMap S (Localization.Away f)))
    (Localization.AtPrime q)).of_isLocalRing

/-- **Stacks 033C.** A smooth algebra over a normal ring is a normal ring. -/
@[stacks 033C]
theorem Algebra.isNormalRing_of_smooth (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (hR : IsNormalRing R) : IsNormalRing S := by
  refine IsNormalRing.of_forall_exists_away fun q _ ↦ ?_
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R)
    (p := q)
  exact ⟨f, hf, IsNormalRing.of_etale (R := MvPolynomial (Fin n) R)
    (isNormalRing_mvPolynomial (Fin n) hR)⟩
