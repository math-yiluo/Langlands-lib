# Renard VI.8.4 Theorem: finite projective modules are locally free

This module proves the published statement
`Langlands.Renard.AlgebraicFamily.LocalFreeCoverStatement` from
[RenardFamilyStatements](RenardFamilyStatements.md), unchanged, as the theorem

```lean
theorem Langlands.Renard.AlgebraicFamily.localFreeCover :
    LocalFreeCoverStatement.{uB, uM}
```

Worker 709 wrote the shared draft proof and its explanation. Worker 1603 checked
the original source, the Mathlib interfaces and the exact target, and prepared
this pair for independent review. Its only project import is the statement module.

## Statement proved

For `B : Type uB` with `[CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
[Algebra.FiniteType ℂ B] [IsReduced B]` and a `B`-module `M : Type uM`:
`M` is finite and projective over `B` if and only if there are `r : ℕ` and
`f : Fin r → B` with `Ideal.span (Set.range f) = ⊤` such that, for every `i`,
`LocalizedModule (Submonoid.powers (f i)) M` is finite and free over
`Localization.Away (f i)`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, VI.8.4, Theorem, printed p. 191 / PDF p. 197. The source
does not prove it. Its proof, printed p. 192 / PDF p. 198, reads "Voir [8],
chapitre II, §5, Théorème 1". Its bibliography entry [8], PDF p. 287, is
N. Bourbaki, *Éléments de mathématique. Fascicule XXVII. Algèbre commutative.
Chapitre 1 : Modules plats. Chapitre 2 : Localisation*, Hermann, Paris, 1961.
Workers 709 and 1603 read PDF pp. 197, 198 and 287; Worker 1603 verified the
registered PDF SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The Lean proof below does not follow
Bourbaki's text, which was not consulted. It goes through Mathlib's free locus.

## Proof

The Lean proof uses only Mathlib. Of the hypotheses on `B` beyond `CommRing`,
it uses only `IsNoetherianRing B`, once, in step 1 of the converse. The
`ℂ`-algebra, finite-type and reduced hypotheses are unused.

**Finite projective implies locally free.** Assume `Module.Finite B M` and
`Module.Projective B M`.

1. `Module.finitePresentation_of_projective` makes `M` finitely presented.
2. Let `T` be the set of `t : B` such that
   `LocalizedModule.Away t M` is finite and free over `Localization.Away t`.
   The proof shows `Ideal.span T = ⊤` by contradiction. Otherwise
   `Ideal.exists_le_maximal` gives a maximal ideal `m` containing `T`. The
   localization `LocalizedModule m.primeCompl M` is finite and flat (indeed
   projective) over the local ring `Localization.AtPrime m`, so it is free by
   `Module.free_of_flat_of_isLocalRing`. Since `M` is finitely presented,
   `Module.FinitePresentation.exists_free_localizedModule_powers` gives
   `t ∉ m` with `LocalizedModule.Away t M` free over `Localization.Away t`.
   That module is finite because `M` is, so `t ∈ T ⊆ m`, a contradiction.
3. `Ideal.span_eq_top_iff_finite` gives a finite set `s ⊆ T` with
   `Ideal.span s = ⊤`. Take `r = s.card` and `f i` the `i`-th element of `s`
   under `s.equivFin`. The range of `f` is `s`, so its span is `⊤`, and each
   `f i` lies in `T`.

**Locally free implies finite projective.** Assume `r`, `f`, the span
condition and that each localization is finite and free.

1. `Module.Finite.of_localizationSpan`, applied to the set `Set.range f`, gives
   `Module.Finite B M`. Then `Module.finitePresentation_of_finite`, which
   needs `IsNoetherianRing B`, makes `M` finitely presented.
2. By `Module.freeLocus_eq_univ_iff`, which needs finite presentation, it
   suffices that every prime `p` lies in `Module.freeLocus B M`.
3. Some `f i` is not in `p`: otherwise `Set.range f ⊆ p`, so
   `⊤ = Ideal.span (Set.range f) ≤ p`, contradicting primality.
4. The localization at `f i` is free, hence projective, so
   `Module.basicOpen_subset_freeLocus_iff` gives
   `PrimeSpectrum.basicOpen (f i) ⊆ Module.freeLocus B M`. The prime `p` lies
   in that basic open set.

## Check

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiles the module
with no errors or warnings. The theorem's axioms are `propext`,
`Classical.choice` and `Quot.sound`, and its universe parameters are `uB` and
`uM`.
