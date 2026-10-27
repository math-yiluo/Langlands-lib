# The comparison theorem for actual Tate cohomology

This module proves `Langlands.Tate.tateComparison : TateComparison.{u}`, the
proposition of module `CohomologicalTrivialityStatement`: let `G : Type u` be a
finite group and `f : D ⟶ E` a morphism in `Rep.{u} IntegralScalar.{u} G`.
Suppose that for every prime `p` and every Sylow `p`-subgroup `P` there is an
integer `m` such that, after restriction to `P`, the map induced by `f` on
actual Tate cohomology is surjective in degree `m`, bijective in degree `m + 1`
and injective in degree `m + 2`. Then the map induced by `f` on
`tateCohomology` is bijective in every integer degree.

It also proves `tateComparison_of`, which derives the same conclusion from the
two other propositions of the statement module, `PGroupTateVanishing` and
`SylowTateVanishing`. The main theorem applies it to their proofs
`pGroupTateVanishing` (module `PGroupTateVanishingProof`) and
`sylowTateVanishing` (module `SylowTateVanishingProof`).

## Source and route

The mathematics is Serre, *Local Fields*, Chapter IX, §7, Theorem 12 (printed
pages 147–148, PDF pages 153–154), in the case `B = ℤ` and for the whole group
`g = G` only. The proof uses the same mapping-cylinder construction. Serre gets
cohomological triviality of the cokernel from Theorem 8. Here Theorem 8 is
replaced by the two weaker facts the argument needs: `PGroupTateVanishing` for
each Sylow subgroup, then `SylowTateVanishing` for `G`.

## Proof

Helper lemmas are in the namespace `Langlands.Tate.Comparison`. A local
instance (`tateCohomologyFunctorAdditive`) records that
`tateCohomologyFunctor n` is additive, as the composite of the Tate complex
functor and a homology functor.

1. **The cylinder.** Let `I := coinduced D` and
   `θ := biprod.lift f (coinducedEmbedding D) : D ⟶ E ⊞ I`. Then `θ` is a
   monomorphism, because `θ ≫ biprod.snd = coinducedEmbedding D` is one. The
   short complex `S := (θ, cokernel.π θ)` is short exact, and
   `θ ≫ biprod.fst = f`.
2. **The projection is invertible on Tate cohomology.** `isIso_map_of_split`
   proves: if `i ≫ pr = 𝟙` and `pr ≫ i + s ≫ j = 𝟙` with `s` mapping into an
   object `I` with zero Tate group, then `pr` induces an isomorphism, with
   inverse induced by `i`. With `biprod.total` this applies to
   `biprod.fst : E ⊞ I ⟶ E`. It is used over `G`, where `I` is acyclic by
   `coinduced_tate_isZero`, and after restriction to a Sylow subgroup `P`,
   where the restricted coinduced module is acyclic by
   `restrictedCoinduced_tate_isZero` (module `SubgroupShifts`).
   `surjective_injective_iff` then shows that `θ ≫ pr` and `θ` are surjective,
   respectively injective, in the same degrees.
3. **The cokernel vanishes on every Sylow subgroup.** Fix `p` and a Sylow
   subgroup `P`. Restriction `Rep.resFunctor P.1.subtype` is exact, so it
   carries `S` to a short exact sequence over `P` (`ShortExact.map_of_exact`).
   By step 2 the hypothesis on `f` at `m`, `m + 1`, `m + 2` becomes the same
   hypothesis on the restriction of `θ`. `cokernel_isZero` uses the long exact
   sequence (`TateCohomology.exact₃` and `TateCohomology.δ_map`) to prove: if
   the first map is surjective in degree `k` and injective in degree `k + 1`,
   then the third term vanishes in degree `k`. Taking `k = m` and
   `k = m + 1`, the restricted cokernel has zero Tate groups in degrees `m`
   and `m + 1`. `PGroupTateVanishing`, applied to the `p`-group `P`, gives
   vanishing in every degree.
4. **The cokernel is acyclic over `G`.** For each degree `k`, step 3 supplies
   the hypothesis of `SylowTateVanishing`, so `tateCohomology (cokernel θ) k`
   is zero.
5. **Conclusion.** `bijective_of_isZero` uses the long exact sequence
   (`TateCohomology.exact₁` and exactness at the middle term, `tate_exact₂`)
   to show that `θ` induces bijections in every degree once the third term of
   a short exact sequence is acyclic. Step 2 over `G` transfers bijectivity
   from `θ` to `θ ≫ biprod.fst = f`.

The declaration check on `Langlands.Tate.tateComparison` reports only the
axioms `propext`, `Classical.choice` and `Quot.sound`.
