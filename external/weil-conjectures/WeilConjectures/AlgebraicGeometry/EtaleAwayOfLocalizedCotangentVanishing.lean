/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import Mathlib.RingTheory.Etale.Locus
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# An étale basic neighbourhood from vanishing of the naive cotangent complex

Source: Stacks Project, Algebra, Tags 07BU, 00TB, 00U1; Morphisms, Tag 02GJ;
More on Algebra, proof of Tag 07M7
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- For a finitely presented `A`-algebra `C`, vanishing at a prime `q` of both the first
homology of the naive cotangent complex and the Kähler differentials gives an étale
principal neighbourhood of `q` over `Spec A`.
Source: Stacks Project, Tags 07BU, 00TB, 00U1, 02GJ, and the proof of 07M7.
(blueprint: theorem-finite-etale-covers-proper-henselian--2)

Proof, following the node's four steps:
1. The zero localized differential module is finite free of rank zero. Together with
vanishing of localized H₁ and finite presentation, this gives `g ∉ q` with `C_g` smooth
by `lem-weil-pbc-smooth-at-prime-naive-cotangent-criterion` (07BU).
2. By `lem-weil-pbc-kahler-differentials-localization` (00RT), the differentials of
`C_g` are the localization of those of `C`. They are finite projective, hence finite,
by `def-weil-pbc-smooth-ring-map`. Their localization at the prime over `q` is zero.
Choose finite generators and an element outside that prime killing each generator;
the product kills the whole module. Write this product as `c/g^k` with `c ∉ q`.
Then `c` kills the differentials of `C_g`. Put `h = g*c`, which is outside `q`.
3. Identify `C_h` with `(C_g)_c`. By
`lem-weil-pbc-smooth-ring-map-principal-localization` (00T3), it is smooth over `A`.
By localization of differentials (00RT), its differentials vanish. Thus it is finitely
presented with H₁ and differentials zero, hence étale as a ring map (00U1).
4. By `lem-weil-pbc-etale-ring-map-iff-etale-affine` (02GJ), its induced map of
spectra is étale, in the sense of `def-weil-etale-morphism`. -/
theorem exists_etale_away_of_localized_cotangent_vanishing
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.FinitePresentation A C] (q : Ideal C) [q.IsPrime]
    (hH : Subsingleton (LocalizedModule q.primeCompl (Algebra.H1Cotangent A C)))
    (hΩ : Subsingleton (LocalizedModule q.primeCompl (KaehlerDifferential A C))) :
    ∃ h : C, h ∉ q ∧
      Etale (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away h)))) := by
  have hq : (⟨q, inferInstance⟩ : PrimeSpectrum C) ∈ Algebra.etaleLocus A C := by
    rw [Algebra.etaleLocus_eq_compl_support]
    exact ⟨Module.notMem_support_iff.mpr hΩ, Module.notMem_support_iff.mpr hH⟩
  have : Algebra.IsEtaleAt A q := hq
  obtain ⟨h, hh, he⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) q
  refine ⟨h, hh, ?_⟩
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  exact (RingHom.etale_algebraMap).mpr he

end AlgebraicGeometry
