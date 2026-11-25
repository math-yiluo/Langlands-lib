/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SurjectiveOnStalks
import WeilConjectures.RingTheory.StrictlyHenselianQuotient
import WeilConjectures.Mathlib.RingTheory.Etale.QuasiFinite

/-! # Strict henselianity of prime localizations of a quotient

Source: Stacks Project, Lemma 09ZC, local-ring step.
-/

@[expose] public section

universe u

/-- Every prime localization of a quotient of a normal domain with separably closed
fraction field is strictly henselian.

Source: Stacks Project, Etale Cohomology, Lemma 09ZC, second sentence of the proof;
Algebra, Lemma 05WS.

Proof: For a prime `p` of `R/I`, let `P` be its preimage in `R`. Then `R_P` is a normal
local domain and has the same fraction field as `R`. Stacks 09Z9 makes it henselian
with separably closed residue field. The localized quotient map identifies `(R/I)_p`
with `R_P / I R_P`. Since `I` is contained in `P`, its extension lies in the maximal
ideal of `R_P`. Apply the strictly henselian quotient theorem (05WS) and transfer
strict henselianity along the displayed ring isomorphism. If `I` is the unit ideal,
there are no primes of `R/I`, so the assertion is vacuous.
(blueprint: lem-weil-pbc-gabber-quotient-localizations)
-/
theorem gabber_quotient_localizations
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (hsep : IsSepClosed (FractionRing R)) (I : Ideal R)
    (p : Ideal (R ⧸ I)) [p.IsPrime] :
    IsStrictlyHenselianLocalRing (Localization.AtPrime p) := by
  let := hsep
  let P := p.comap (Ideal.Quotient.mk I)
  let A := Localization.AtPrime P
  have hP : P.primeCompl ≤ nonZeroDivisors R := P.primeCompl_le_nonZeroDivisors
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A P.primeCompl hP
  let g : A →+* FractionRing R :=
    IsLocalization.map _ (T := nonZeroDivisors R) (RingHom.id R) hP
  let := g.toAlgebra
  have : IsScalarTower R A (FractionRing R) := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp,
      RingHomCompTriple.comp_eq])
  have : IsFractionRing A (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isLocalization P.primeCompl A (FractionRing R) hP
  have : HenselianLocalRing A :=
    HenselianLocalRing.of_isSepClosed_fractionRing (FractionRing R)
  have : IsStrictlyHenselianLocalRing A :=
    ⟨IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing (FractionRing R)⟩
  let φ : A →+* Localization.AtPrime p :=
    Localization.localRingHom P p (Ideal.Quotient.mk I) rfl
  have hφ : Function.Surjective φ :=
    RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective p inferInstance
  have hker : RingHom.ker φ ≤ IsLocalRing.maximalIdeal A := by
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    have hz : φ a = 0 := ha
    exact (hu.map φ).ne_zero hz
  obtain ⟨_, _, _, hstrict, _, _⟩ :=
    isStrictlyHenselianLocalRing_quotient.{u, u} A inferInstance (RingHom.ker φ) hker
  let := hstrict
  exact IsStrictlyHenselianLocalRing.of_ringEquiv (φ.quotientKerEquivOfSurjective hφ)
