# Proof: injective character and cocharacter maps give an isogeny of split tori

Authors: Worker 1428 (proof), Worker 1520 (recheck against the published statement and submission).

`Langlands.GroupScheme.splitTorusIsogenyOfLatticeMaps` proves the proposition
`Langlands.GroupScheme.SplitTorusIsogenyOfLatticeMapsStatement.{u}`
(module `Rational/SplitTorusIsogenyOfLatticeMapsStatement`). For every field
`k`, split tori `T` and `T'` over `Spec k` and every homomorphism `t : T ⟶ T'`
with injective character map `χ ↦ t ≫ χ` and injective cocharacter map
`ν ↦ ν ≫ t`, the underlying morphism of `t` is finite, flat and surjective
(`IsIsogeny`). The module proves three helper results on the way.

## Helper results

- `finite_quotient_range_of_injective_of_card_le`: an injective ℤ-linear map
  `f : ℤ^J → ℤ^I` with `|I| ≤ |J|` has finite cokernel. Its range has
  `finrank` `|J|` (`LinearMap.finrank_range_of_inj`). By rank–nullity
  (`Submodule.finrank_quotient_add_finrank`), the quotient `ℤ^I / range f`
  has `finrank` `0`, so every element is killed by a nonzero integer
  (`Module.finrank_eq_zero_iff`). A finitely generated torsion ℤ-module is
  finite (`Module.finite_of_fg_torsion`).
- `Diagonalizable.finite_mapDomainRingHom`: for an injective homomorphism
  `g : Λ' →+ Λ` of abelian groups with `Λ / g(Λ')` finite, the group-algebra
  map `R[Λ'] → R[Λ]` is finite. The published `cosetLinearMap_bijective`
  (`Torus/DiagonalizableFaithfullyFlat`) identifies `R[Λ]` with the free
  `R[Λ']`-module on the finite set `Λ / g(Λ')`.
- `splitTorus.isIsogeny_of_characterMap`: a homomorphism
  `f : splitTorus I ⟶ splitTorus J` of standard split tori whose integral
  character map `characterMap I J f : ℤ^J → ℤ^I` is injective with finite
  cokernel is an isogeny. The published `diagonalizableMap_splitIso` writes
  `f` as `eI⁻¹ ≫ diagonalizableMap I J f ≫ eJ`, with the standard
  isomorphisms `eI`, `eJ` from the diagonalizable models. By
  `diagonalizableMap_hom_left` and `Diagonalizable.incl_toRingHom`, the
  underlying morphism of `diagonalizableMap I J f` is `Spec` of the
  group-algebra map along `characterMap I J f`. That ring map is faithfully
  flat (`Diagonalizable.faithfullyFlat_mapDomainRingHom`), so the morphism
  is flat and surjective (`flat_and_surjective_SpecMap_iff`). It is finite
  by the previous helper (`IsFinite.SpecMap_iff`). Isomorphisms are central
  isogenies (`isCentralIsogeny_of_isIso`), and isogenies compose
  (`IsIsogeny.comp`).

## Main proof

Choose isomorphisms `eA : T ≅ splitTorus I` and `eT : T' ≅ splitTorus J`
(the definition of `IsSplitTorus`). Let
`q = eA⁻¹ ≫ groupHom t ≫ eT`.

1. The character map of `q` is injective. By `characterMap_equiv`, it sends
   the coordinates of `χ` to those of `eA⁻¹ ≫ t ≫ eT ≫ χ`. Cancelling the
   isomorphisms and applying the injectivity hypothesis on `t ≫ ·` recovers
   `χ`.
2. The cocharacter map `splitTorus.cocharacterMap I J q` is injective, by the
   same cancellation with the injectivity hypothesis on `· ≫ t`.
3. Injective ℤ-linear maps between free modules do not increase `finrank`
   (`LinearMap.finrank_le_finrank_of_injective`). So step 1 gives
   `|J| ≤ |I|` and step 2 gives `|I| ≤ |J|`. The first helper then shows
   that the character map of `q` has finite cokernel.
4. By the third helper, `q` is an isogeny. Since
   `groupHom t = eA ≫ q ≫ eT⁻¹`, so is `t`.

## Provenance

The statement and its source argument are in the statement's Markdown
(Milne, *Algebraic Groups*, 2017, source `milne-2017-algebraic-groups`:
the remark after Definition 23.1, printed p.484; Theorem 12.9, printed
p.233). The Lean route is internal and follows that argument in coordinates:
the two injectivity hypotheses give equal ranks and a finite cokernel, and
the coordinate ring of `T` is a finite free module over that of `T'`. The
algebraic inputs are published Library results and Mathlib.

Checked with `lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
against the published statement (Library commit
`ee0c0dd6da0a631f199c2bc0aa6040eece98f41d`; diagnostic
`8f8b34f2-2bfa-4fb7-b236-cc579d1d6afd`, Lake build): 0 errors, 0 warnings,
axioms `propext`, `Classical.choice`, `Quot.sound`.
