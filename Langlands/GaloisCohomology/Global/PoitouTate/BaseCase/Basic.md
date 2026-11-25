# The base case of Poitou–Tate duality: the formal hypotheses

`Langlands/GaloisCohomology/Global/PoitouTate/BaseCase/Basic.lean`, namespace `Langlands.GaloisCohomology.PoitouTate.Internal`.

For a number field `K` containing the `n`-th roots of unity, `S` a finite set of finite places
containing the places above `n`, `n` odd or `K` totally complex, this file proves the hypotheses of
the abstract base case (`BaseDualityHypotheses`) that do not involve class field theory:

* `G_S` acts trivially on `μ_n(K_S)` (`dualizingModule_ρ_apply_of_mem`);
* the local traces `localTrace` (the local invariants with values in `ℤ/n`) and the global trace
  `finiteTrace` agree on the local terms (`finiteTrace_ptLocalToCompact`);
* `H³(G_S, ℤ/n) = H³(G_S, μ_n) = 0`, `H¹(G_S, ℤ/n)` and `H_c²(G_S, μ_n)` are finite;
* the two pairings `H_c¹(G_S, μ_n) × H²(G_S, ℤ/n)` and `H_c²(G_S, ℤ/n) × H¹(G_S, μ_n)` agree through
  `H_c → H` (`finiteTrace_compactCupRes_swap`), by the graded commutativity of the cup products with
  compact support (`compactCupRes_eq_neg_one_pow_smul_compactCupRightRes`).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.Internal.braiding_comp_zmodMulPairingRight.{u} {G : Type u} [Group G] {n : ℕ}
  (D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) (hD : ∀ (d : ↑D), n • d = 0) :
  CategoryTheory.CategoryStruct.comp (β_ (Langlands.ProfiniteCohomology.zmodRep G n) D).hom
      (Langlands.GaloisCohomology.zmodMulPairingRight n D hD) =
    Langlands.ProfiniteCohomology.zmodMulPairing n D hD
Langlands.GaloisCohomology.PoitouTate.Internal.compactCupRes_zmodMulPairingRight_swap.{u} {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G) {n : ℕ}
  (D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) [Langlands.IsSmoothRep D] (hD : ∀ (d : ↑D), n • d = 0)
  (hsurj :
    Function.Surjective
      ⇑(ModuleCat.Hom.hom
          (Langlands.GaloisCohomology.localToCompact φ D (fun v => Rep.res (↑(φ v)) D)
            (fun x => CategoryTheory.CategoryStruct.id (Rep.res (↑(φ x)) D)) 2)))
  (yc : ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes φ D 1))
  (xc : ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes φ (Langlands.ProfiniteCohomology.zmodRep G n) 2)) :
  ((Langlands.GaloisCohomology.compactCupRes φ (Langlands.GaloisCohomology.zmodMulPairingRight n D hD) ⋯) yc)
      ((ModuleCat.Hom.hom
          (Langlands.GaloisCohomology.compactToGlobal φ (Langlands.ProfiniteCohomology.zmodRep G n)
            (fun v => Rep.res (↑(φ v)) (Langlands.ProfiniteCohomology.zmodRep G n))
            (fun x => CategoryTheory.CategoryStruct.id (Rep.res (↑(φ x)) (Langlands.ProfiniteCohomology.zmodRep G n)))
            2))
        xc) =
    ((Langlands.GaloisCohomology.compactCupRes φ (Langlands.ProfiniteCohomology.zmodMulPairing n D hD) ⋯) xc)
      ((ModuleCat.Hom.hom
          (Langlands.GaloisCohomology.compactToGlobal φ D (fun v => Rep.res (↑(φ v)) D)
            (fun x => CategoryTheory.CategoryStruct.id (Rep.res (↑(φ x)) D)) 1))
        yc)
Langlands.GaloisCohomology.PoitouTate.Internal.dualizingModule_ρ_apply_of_mem.{u} {K Ω : Type u} [Field K] [Field Ω]
  [Algebra K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ)
  (hμ : ∀ (ζ : Ω), ζ ^ n = 1 → ζ ∈ (algebraMap K Ω).range) (g : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)
  (d : ↑(Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n)) :
  ((Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n).ρ g) d = d
Langlands.GaloisCohomology.PoitouTate.Internal.finiteTrace_ptLocalToCompact.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n] [Finite ↑S]
  (hK : Odd n ∨ NumberField.IsTotallyComplex K)
  (ξ :
    (v : ↑S) →
      ↑(Langlands.ProfiniteCohomology.cohomology
          (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) ↑v)
          2)) :
  (Langlands.GaloisCohomology.PoitouTate.finiteTrace ι S n hK)
      ((ModuleCat.Hom.hom
          (Langlands.GaloisCohomology.ptLocalToCompact (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
            (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) 2))
        ξ) =
    ∑ v, (Langlands.GaloisCohomology.PoitouTate.Internal.localTrace ι S n ↑v) (ξ v)
Langlands.GaloisCohomology.PoitouTate.Internal.finite_cohomology_one_zmodRep.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n] [Finite ↑S]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) :
  Finite
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1)
Langlands.GaloisCohomology.PoitouTate.Internal.finite_compactSupportCohomologyRes_two.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n] [Finite ↑S]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) :
  Finite
    ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) 2)
Langlands.GaloisCohomology.PoitouTate.Internal.localTrace.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) v)
        2) →+
    ZMod n
Langlands.GaloisCohomology.PoitouTate.Internal.neg_one_pow_one_mul_two_smul.{u_1, u_2} {R : Type u_1} {M : Type u_2}
  [Ring R] {x✝ : AddCommGroup M} {x✝¹ : Module R M} (x : M) : (-1) ^ (1 * 2) • x = x
Langlands.GaloisCohomology.PoitouTate.Internal.subsingleton_cohomology_three_dualizingModule.{u} {K Ω : Type u}
  [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K) :
  Subsingleton
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) 3)
Langlands.GaloisCohomology.PoitouTate.Internal.subsingleton_cohomology_three_zmodRep.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K) :
  Subsingleton
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 3)
Langlands.GaloisCohomology.PoitouTate.Internal.zmodToQZ_localTrace.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (x :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) v)
        2)) :
  (Langlands.ProfiniteCohomology.zmodToQZ n) ((Langlands.GaloisCohomology.PoitouTate.Internal.localTrace ι S n v) x) =
    (Langlands.GaloisCohomology.PoitouTate.invariantAt ι S n v) x
```

## Outline of the proofs

Triviality of the action: the roots of unity come from `K`. Vanishing in degree `3`: `cohomologicalDimensionStatement`. Finiteness: `finite_cohomology_of_nsmul`, `Local.finite_cohomology` and the exact sequence `∏ H¹ → H_c² → H²` (`finite_of_exact_of_finite` of the module `Langlands.Cohomology.Profinite.Duality.DualModule`). The swap: `compactCupRes_eq_neg_one_pow_smul_compactCupRightRes` (sign `(-1)^{1·2} = 1`) and `compactCup_eq_compactCupRight` of the Library.

## Declarations

`neg_one_pow_one_mul_two_smul`, `braiding_comp_zmodMulPairingRight`, `compactCupRes_zmodMulPairingRight_swap`, `dualizingModule_ρ_apply_of_mem`, `localTrace`, `zmodToQZ_localTrace`, `finiteTrace_ptLocalToCompact`, `subsingleton_cohomology_three_zmodRep`, `subsingleton_cohomology_three_dualizingModule`, `finite_cohomology_one_zmodRep`, `finite_compactSupportCohomologyRes_two`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseSwap.lean` (the swap). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). 

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
