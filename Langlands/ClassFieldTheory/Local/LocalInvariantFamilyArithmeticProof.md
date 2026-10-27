# Arithmetic normalization of the local invariant family

Author: Worker 272.

This module proves the published proposition
`Langlands.ClassFieldTheory.Local.LocalInvariantFamilyArithmeticStatement`
(module `Langlands.ClassFieldTheory.Local.LocalInvariantFamilyLawsStatement`).
The exact-target theorem is

```
theorem localInvariantFamilyArithmetic :
    LocalInvariantFamilyArithmeticStatement.{u}
```

in the namespace `Langlands.ClassFieldTheory.Local`. Unfolded, it says: for
every proof `hEx : UnramifiedH2Exhaustion.{u}`, every prime `p`, every p-adic
field `F`, every finite Galois extension `L/F`, every `n` with `NeZero n`, every
`χ : Gal(L/F) ≃* Multiplicative (ZMod n)` with
`IsArithmeticUnramifiedCoordinate F L χ`, and every unit `a` of `F` with
`F.canonicalTopologicalData.ord a = 1`,

```
(localInvariantFamily hEx p).relative F L (cyclicClass F.Carrier L χ.toMonoidHom a) =
  reciprocalClass n.
```

## Source

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer, 1979 (registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`),
Chapter XIII, §3 (printed page 193, PDF page 198). Serre writes `inv_K` on the
unramified part as `γ ∘ δ⁻¹ ∘ β ∘ α⁻¹`. Here `β` is induced by the valuation,
`δ` is the coboundary of `0 → ℤ → ℚ → ℚ/ℤ → 0`, and `γ` evaluates a character
at the arithmetic Frobenius `F`. For an unramified extension of degree `n`,
this sends the class built from a uniformizer and the Frobenius coordinate to
`1/n`.

The Library implements this formula for finite unramified stages. It is
`unramifiedH2Invariant`, evaluated on cyclic classes by
`UnramifiedInflation.unramifiedH2Invariant_cyclicClass` (module
`UnramifiedInvariantInflationProof`). The proof below shows that the family's
relative invariant of `L` is that finite unramified invariant.

## Lemmas in `ArithmeticNormalizationProof`

All p-adic fields below carry their canonical topological data.

- `canonicalNorm_algEquiv`: an isomorphism `σ` over `Padic p` of p-adic fields
  preserves the canonical norm. The canonical norm is Mathlib's
  `spectralNorm`, that is `spectralValue` of the minimal polynomial over
  `Padic p`, and `minpoly.algEquiv_eq` says `σ` preserves minimal polynomials.
- `integers_map`, `integersEquiv`: `σ` maps the canonical integer ring onto the
  canonical integer ring. Membership is `canonicalNorm ≤ 1`
  (`canonicalNorm_le_one_iff_mem_integers`). `integersEquiv` is the resulting
  ring isomorphism (`RingEquiv.subringMap` followed by
  `RingEquiv.subringCongr`).
- `ramificationIndex_eq_of_algEquiv`: `σ` preserves the absolute ramification
  index. The residue fields are isomorphic (`ResidueField.mapEquiv`), so the
  residue cardinalities agree. By `residueCardinality_eq_pow` the residue
  degrees agree. The degrees over `Padic p` agree, by
  `σ.toLinearEquiv.finrank_eq`. Now `ramificationIndex_mul_residueDegree`
  (`e · f` is the degree over `Padic p`) gives equal ramification indices.
- `ramificationIndex_eq_of_residueHom_injective`: let `E/F` be finite Galois
  (p-adic fields, with the scalar tower over `Padic p`). If the residue action
  `LocalGalois.residueHom F.Carrier E.Carrier` is injective, then `F` and `E`
  have the same absolute ramification index. The residue action is always
  surjective (`LocalGalois.residueHom_surjective`), so it is bijective.
  Comparing Galois group orders (`IsGalois.card_aut_eq_finrank`) gives
  `[l:k] = [E:F]` for the residue fields. The residue field comparisons
  `ArithmeticCoordinate.extensionResidueEquiv` and `baseResidueEquiv` (module
  `UnramifiedArithmeticProof`) and `Module.natCard_eq_pow_finrank` give
  `q_E = q_F ^ [E:F]`. So `f_E = f_F · [E:F]`. With
  `ramificationIndex_mul_residueDegree` for `E` and `F` and the tower formula
  `Module.finrank_mul_finrank`, this gives `e_E · f_F · [E:F] =
  e_F · f_F · [E:F]`, so `e_E = e_F`. The file repeats the local normed-field
  and residue-finiteness instances of `UnramifiedArithmeticProof`, so its
  residue action is the one in `IsArithmeticUnramifiedCoordinate`.
- `relativeInflation_eq_relativeH2Equiv`: let `L/K` be normal and `K ⊆ L ⊆ M`
  a tower whose inclusion `L → M` is an isomorphism `e`. Then
  `relativeInflation K L M 2 x = relativeH2Equiv e x`. The proof shows that
  normal restriction of `s` in `Gal(M/K)` is `relativeAutPullback e s`
  (`AlgEquiv.restrictNormal_commutes`). The cocycle comparison then follows as
  in the other transport lemmas (`groupCohomology.H2π_comp_map_apply`,
  `relativeH2Equiv_H2π`, `groupCohomology.cocycles₂_ext`).

## The implemented proof of the target

After introducing the data:

1. `n = [L:F]`. `χ` is a bijection onto `Multiplicative (ZMod n)`, so
   `IsGalois.card_aut_eq_finrank` and `Nat.card_zmod` give the equality. The
   proof substitutes `n := Module.finrank F.Carrier L`.
2. `L` as a p-adic field. The proof gives `L` the composite algebra
   `Padic p → F → L`, its scalar tower and finiteness over `Padic p`. Then
   `L' : PadicField p := ⟨L⟩` has carrier `L`.
3. `L` is unramified. The first component of the arithmetic hypothesis is
   injectivity of the residue action, so
   `ramificationIndex_eq_of_residueHom_injective F L'` gives
   `hFL : e_F = e_{L'}`.
4. The image stage. Let `f := closureEmbedding F.Carrier L`,
   `e := f.equivFieldRange`, `S₀ := ⟨f.fieldRange, _⟩` (a
   `FiniteIntermediateExtension`), and `E' := S₀.asPadicField`. `e` is also an
   isomorphism over `Padic p`, `σ : L'.Carrier ≃ₐ[Padic p] E'.Carrier`
   (`AlgEquiv.ofRingEquiv` with `e.commutes`). So
   `ramificationIndex_eq_of_algEquiv σ` and `hFL` give `hFE : e_F = e_{E'}`.
   This makes `S : Stage F := ⟨S₀, _, hFE⟩` a stage of
   `AbsoluteInvariantAssembly`.
5. Left side. Unfolding (`localInvariantFamily_relative`,
   `embeddedRelativeInvariant_apply`) gives the descended invariant of
   `closureInflation F.Carrier S.field 2 (relativeH2Equiv e c)`, where `c` is
   the cyclic class. By `descendedHom_stage` (module
   `AbsoluteInvariantAssembly`) this is `S.invariant (relativeH2Equiv e c)`.
   By definition that is
   `unramifiedH2Invariant F E' hFE S.coordinate (relativeH2Equiv e c)`.
6. Inflation. With the algebra `L → E'` given by `e`, the lemma
   `relativeInflation_eq_relativeH2Equiv` rewrites `relativeH2Equiv e c` as
   `relativeInflation F.Carrier L E'.Carrier 2 c`. The published
   `unramifiedInvariantInflationCompatibility` (module
   `UnramifiedInvariantInflationProof`), applied to `F`, `L'`, `E'`, `hFL`,
   `hFE`, the coordinates `χ` and `S.coordinate` and their arithmetic
   certificates `hχ` and `S.coordinate_arithmetic`, turns this into
   `unramifiedH2Invariant F L' hFL χ c`.
7. Value. `UnramifiedInflation.unramifiedH2Invariant_cyclicClass` with the
   published `cyclicClassNormNormalization` gives
   `rationalClass (ord a / [L:F])`. With `ord a = 1` this is
   `rationalClass ([L:F]⁻¹) = reciprocalClass [L:F]`.

## Notes

- The module imports only published modules.
- Axioms used by the target theorem: `propext`, `Classical.choice`,
  `Quot.sound`.
