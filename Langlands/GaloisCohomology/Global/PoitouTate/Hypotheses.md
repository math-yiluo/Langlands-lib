# The hypotheses of the abstract Poitou–Tate theorems for `G_S`

`Langlands/GaloisCohomology/Global/PoitouTate/Hypotheses.lean`, namespace `Langlands.GaloisCohomology.PoitouTate`.

The abstract nine-term sequence with Tate's `Ĥ⁰` (`TatePoitouTateHypotheses` of
`Langlands.GaloisCohomology.CompactSupport.TateModified.NineTerm`) needs, for a profinite group with
two families of local groups, a dualizing module `D ≅ ℤ/N`, a trace and local invariants:
the duality with compact support for finite modules killed by `N`, finiteness in degrees `≤ 2`,
the compatibility of the trace with the local invariants, injectivity of `H⁰` into the first family,
and the surjectivity of the local pairings.

For `G_S` with the localizations at the places of `S` and at the real places, `D = μ_N`, the trace
`trace` and the invariants `invariantAt`, `realInvariantAt`, this file proves all of these except one,
which enters as the hypothesis of `tatePoitouTateHypotheses_of`: the duality with compact support
itself. The others come from:

* `μ_N(K_S) ≅ ℤ/N` because `K_S` contains the `N`-th roots of unity (`nonempty_addEquiv_dualizingModule`);
* finiteness: `finite_cohomology` of `Langlands.GaloisCohomology.Global.RealPlaces.HighDegree`, with
  the places above `#M` inside those above `N` (`natCast_mem_of_natCard_mem`);
* the trace: `trace_localToCompact`;
* `H⁰`: `S` is not empty when `N ≠ 1` (`nonempty_of_natCast_mem`), and restriction in degree `0` is
  injective;
* the real places: `surjective_realPairing_zero`, `exists_realPairing_two`;
* the finite places: `surjective_localPairing` (local Tate duality, `localTateDualityStatement`).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.exists_prime_dvd_natCast_mem.{u_1} {R : Type u_1} [CommRing R] (P : Ideal R)
  [P.IsPrime] {n : ℕ} (hn : n ≠ 0) (h : ↑n ∈ P) : ∃ p, Nat.Prime p ∧ p ∣ n ∧ ↑p ∈ P
Langlands.GaloisCohomology.PoitouTate.injective_ptRes_zero.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Nonempty ↑S]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M] :
  Function.Injective fun x v =>
    (Langlands.GaloisCohomology.ptRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S) M v 0) x
Langlands.GaloisCohomology.PoitouTate.natCast_mem_of_natCard_mem.{u, u_1} {K : Type u} [Field K] {A : Type u_1}
  [AddCommGroup A] [Finite A] {N : ℕ} (hA : ∀ (a : A), N • a = 0)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (hv : ↑(Nat.card A) ∈ v.asIdeal) :
  ↑N ∈ v.asIdeal
Langlands.GaloisCohomology.PoitouTate.nonempty_addEquiv_dualizingModule.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {N : ℕ} [NeZero N]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S) :
  Nonempty (↑(Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) ≃+ ZMod N)
Langlands.GaloisCohomology.PoitouTate.nonempty_of_natCast_mem.{u} {K : Type u} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {N : ℕ} (hN : N ≠ 1)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S) : Nonempty ↑S
Langlands.GaloisCohomology.PoitouTate.tatePoitouTateHypotheses_of.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S) (hN : N ≠ 1)
  (hdual :
    ∀ (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
      [inst : Langlands.IsSmoothRep M] [inst_1 : Finite ↑M],
      (∀ (m : ↑M), N • m = 0) →
        ∀ {r s : ℕ} (h : r + s = 3),
          1 ≤ s →
            Function.Bijective
              ⇑(Langlands.GaloisCohomology.tateCompactDualityMap (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
                  (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
                  (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) h
                  (Langlands.GaloisCohomology.PoitouTate.trace ι S N) M)) :
  Langlands.GaloisCohomology.TatePoitouTateHypotheses (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
    (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
    (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) (Langlands.GaloisCohomology.PoitouTate.trace ι S N)
    (fun v => Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v) fun w =>
    Langlands.GaloisCohomology.PoitouTate.realInvariantAt ι S N ↑w
```

## Outline of the proofs

Each field of `TatePoitouTateHypotheses` is supplied by a Library theorem: finiteness (`finite_cohomology`), the trace on local terms (`trace_localToCompact`), injectivity in degree `0` (`injective_map_zero`), the local pairings at the finite places (`surjective_localPairing`, from `localTateDualityStatement`) and at the real places (`surjective_realPairing_zero`, `exists_realPairing_two`); the duality itself is the hypothesis `hdual`.

## Declarations

`exists_prime_dvd_natCast_mem`, `natCast_mem_of_natCard_mem`, `nonempty_of_natCast_mem`, `nonempty_addEquiv_dualizingModule`, `injective_ptRes_zero`, `tatePoitouTateHypotheses_of`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
