/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # A closed presentation of a principal open in a quotient spectrum

Source: Stacks Project, Etale Cohomology, Lemma 09ZC, principal-open step.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- A principal open in the spectrum of a quotient of a normal domain with separably
closed fraction field is itself a closed subscheme of the spectrum of such a domain.

Source: Stacks Project, Etale Cohomology, Lemma 09ZC, third and fourth sentences.

Proof: Lift `h` to `f` in `R`. If `f = 0`, then `h = 0`; its principal open is the
empty scheme, whose unique map to `Spec R` is a closed immersion, so take `S = R`.
If `f` is nonzero, take `S = R_f`. This localization is a domain and integrally closed,
and its fraction field is isomorphic to that of `R`, hence separably closed. The
surjection `R_f` onto `(R/I)_h` follows from localization commuting with quotients.
Its spectrum map is a closed immersion. The spectrum of `(R/I)_h` is isomorphic to
the open subscheme `D(h)` of `Spec (R/I)`, and composing with this isomorphism gives
the required closed immersion. For the unit ideal, all the opens are empty; the same
argument applies without imposing a nontriviality assumption on the quotient.
(blueprint: lem-weil-pbc-gabber-principal-open-closed-presentation)
-/
theorem gabber_principal_open_closed_presentation
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (hsep : IsSepClosed (FractionRing R)) (I : Ideal R) (h : R ⧸ I) :
    ∃ (S : CommRingCat.{u}) (_ : IsDomain S) (_ : IsIntegrallyClosed S)
      (_ : IsSepClosed (FractionRing S)),
      ∃ i : (Scheme.Opens.toScheme (X := Spec (CommRingCat.of (R ⧸ I)))
        (PrimeSpectrum.basicOpen h)) ⟶ Spec S, IsClosedImmersion i  := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective h
  by_cases hf : f = 0
  · subst f
    let U := Scheme.Opens.toScheme (X := Spec (CommRingCat.of (R ⧸ I)))
      (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I 0))
    have : IsEmpty U := ⟨fun x ↦ by simpa using x.property⟩
    refine ⟨CommRingCat.of R, inferInstance, inferInstance, hsep, ?_⟩
    exact ⟨(isInitialOfIsEmpty (X := U)).to _, inferInstance⟩
  · let A := Localization.Away f
    have hP := powers_le_nonZeroDivisors_of_noZeroDivisors hf
    have : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors A hP
    have : IsIntegrallyClosed A :=
      isIntegrallyClosed_of_isLocalization A (Submonoid.powers f) hP
    let g : A →+* FractionRing R :=
      IsLocalization.map _ (T := nonZeroDivisors R) (RingHom.id R) hP
    let := g.toAlgebra
    have : IsScalarTower R A (FractionRing R) := IsScalarTower.of_algebraMap_eq'
      (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp,
        RingHomCompTriple.comp_eq])
    have : IsFractionRing A (FractionRing R) :=
      IsFractionRing.isFractionRing_of_isLocalization
        (Submonoid.powers f) A (FractionRing R) hP
    let := hsep
    have hA : IsSepClosed (FractionRing A) :=
      IsSepClosed.of_ringEquiv (FractionRing.algEquiv A (FractionRing R)).symm.toRingEquiv
    let φ := Localization.awayMap (Ideal.Quotient.mk I) f
    have hφ : Function.Surjective φ := by
      apply Localization.awayMap_surjective_iff.mpr
      intro a
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective a
      exact ⟨b, 0, by simpa using hb⟩
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
      IsClosedImmersion.spec_of_surjective _ hφ
    refine ⟨CommRingCat.of A, inferInstance, inferInstance, hA,
      (basicOpenIsoSpecAway (R := CommRingCat.of (R ⧸ I))
        (Ideal.Quotient.mk I f)).hom ≫
        Spec.map (CommRingCat.ofHom φ), inferInstance⟩

end AlgebraicGeometry
