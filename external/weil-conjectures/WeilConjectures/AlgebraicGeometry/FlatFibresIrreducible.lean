/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-! # Flat finite-presentation maps with dense irreducible fibres

Source: Stacks Project, Algebra, Lemma 00I6 (algebra-lemma-flat-fibres-irreducible)
(blueprint: lem-weil-pbc-flat-fibres-irreducible)
-/

@[expose] public section

/--
For a flat finitely presented algebra over an irreducible ring, irreducibility of
fibres over a dense set of primes implies irreducibility of the total spectrum.
Source: Stacks Project, Algebra, Lemma 00I6 (algebra-lemma-flat-fibres-irreducible)
(blueprint: lem-weil-pbc-flat-fibres-irreducible).
Proof: flatness and finite presentation make the induced map
`PrimeSpectrum T → PrimeSpectrum R` open by
`lem-weil-pbc-flat-finite-presentation-open` (Stacks Tag 00I1).
For each prime `p`, its set-theoretic fibre is homeomorphic to the spectrum of
`p.asIdeal.Fiber T` by `lem-weil-pbc-fibre-spec-homeomorphism` (Stacks Tag 00E6).
Thus `hdense` gives irreducible topological fibres over a dense set of primes.
Apply `lem-weil-pbc-irreducible-on-top` (Stacks Tag 004Z) to this open map and
the irreducible base `hR` to obtain irreducibility of the total spectrum.
Nonemptiness follows by choosing a prime in the dense set (the base is nonempty)
and then a point in its nonempty irreducible fibre.
-/
theorem flat_finitePresentation_dense_irreducible_fibres
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    (hR : IsIrreducible (Set.univ : Set (PrimeSpectrum R)))
    (hflat : (algebraMap R T).Flat)
    (hfp : (algebraMap R T).FinitePresentation)
    (hdense : ∃ U : Set (PrimeSpectrum R), Dense U ∧
      ∀ p ∈ U, IsIrreducible (Set.univ : Set (PrimeSpectrum (p.asIdeal.Fiber T)))) :
    IsIrreducible (Set.univ : Set (PrimeSpectrum T)) := by
  let f := PrimeSpectrum.comap (algebraMap R T)
  have : Module.Flat R T := RingHom.flat_algebraMap_iff.mp hflat
  have : Algebra.FinitePresentation R T := RingHom.finitePresentation_algebraMap.mp hfp
  have hopen : IsOpenMap f :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  obtain ⟨U, hU_dense, hU⟩ := hdense
  have hfibre (p : PrimeSpectrum R) (hp : p ∈ U) : IsIrreducible (f ⁻¹' {p}) := by
    let e := PrimeSpectrum.preimageHomeomorphFiber R T p
    have h := (hU p hp).image (fun q ↦ (e.symm q).val)
      (continuous_subtype_val.comp e.symm.continuous).continuousOn
    have heq : (fun q ↦ (e.symm q).val) '' Set.univ = f ⁻¹' {p} := by
      ext q
      constructor
      · rintro ⟨z, _, rfl⟩
        exact (e.symm z).property
      · intro hq
        exact ⟨e ⟨q, hq⟩, Set.mem_univ _, by simp⟩
    rwa [heq] at h
  have hpre : (Set.univ : Set (PrimeSpectrum R)) ⊆
      closure ((Set.univ : Set (PrimeSpectrum R)) ∩
        {p | IsPreirreducible (f ⁻¹' {p})}) := by
    have hsub : U ⊆ Set.univ ∩ {p | IsPreirreducible (f ⁻¹' {p})} := by
      intro p hp
      exact ⟨Set.mem_univ _, (hfibre p hp).isPreirreducible⟩
    intro p _
    exact closure_mono hsub (hU_dense p)
  have hpre' := hR.isPreirreducible.preimage_of_dense_isPreirreducible_fiber f hopen hpre
  have : Nonempty (PrimeSpectrum R) := hR.nonempty.to_subtype.map Subtype.val
  obtain ⟨p, hp⟩ := hU_dense.nonempty
  obtain ⟨q, _⟩ := (hfibre p hp).nonempty
  exact ⟨⟨q, Set.mem_univ _⟩, by simpa using hpre'⟩
