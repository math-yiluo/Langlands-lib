# Proof of the replaced normalizer-coset lemma

This unit proves the published target
`Langlands.Geometry.Building.UnipotentNormalizerCosetStatement` of
`Langlands/Geometry/Building/IwahoriWeylStatement.lean`. The theorem
`Langlands.Geometry.Building.unipotentNormalizerCoset` is stated at an arbitrary universe `u`.
Its type is exactly `UnipotentNormalizerCosetStatement.{u}`, so no hypothesis is changed or
added.

## What is proved

The target is Kaletha–Prasad Lemma 5.3.5 in the form that replaces it in the authors'
corrections of 1 November 2024. It quantifies over every nonarchimedean local field `F` and
every affine group scheme `G` over `F`. For every `P : ParahoricBuildingData G` it assumes that
`𝒪[F]` is Henselian, that the residue field `𝓀[F]` is perfect, and that
`P.apartment.SatisfiesApartmentAxioms P.centralizer` holds. Then, for every chamber `C` of
`P.affineRoots` and every generic cocharacter `ν` of `P.S`, it gives
`P.UnipotentNormalizerCoset C ν`:

for all `n, n'` in `normalizerPoints P.i` (the actual `N(F)`), there are
`u ∈ standardUnipotentPoints P.i ν ∅` and `p ∈ P.parahoric C` with `n = u * n' * p` if and only
if `n' * n⁻¹ ∈ P.normalizerZero`, the image of the actual `Z(F)^0` in `N(F)`.

The unipotent factor is the literal `standardUnipotentPoints P.i ν ∅`. The parahoric factor is
the full chamber parahoric `P.parahoric C`. The orientation is `n' n⁻¹`, as in the target.

## The implemented proof

The proof applies the published per-data theorem
`ParahoricBuildingData.unipotentNormalizerCoset_of_chamberIwahori` (module
`Langlands/Geometry/Building/UnipotentNormalizerCosetReduction.lean`) to `P`, `C`, `ν`, the
retained apartment axioms, the chamber hypothesis and the genericity hypothesis. That theorem
needs two further inputs. Both are published proofs that hold for every actual `P`, with no
hypotheses:

| Input of the reduction | Library proof |
| --- | --- |
| instance `[P.normalizerZero.Normal]` (`Z(F)^0` normal in `N(F)`) | `ParahoricBuildingData.normal_normalizerZero` (module `ZeroSubgroupCommutatorNormality`) |
| `P.ChamberIwahoriDecompositionStatement` (KP 7.4.9 chamber Iwahori products) | `ParahoricBuildingData.chamberIwahoriDecomposition` (module `ChamberIwahoriProof`) |

The Markdown of `UnipotentNormalizerCosetReduction` describes the reduction in detail. In
outline:

* **Easy direction.** If `n' n⁻¹ ∈ Z(F)^0`, normality gives `n'⁻¹ n ∈ Z(F)^0`. Since
  `Z(F)^0 ⊆ P_C`, take `u = 1` and `p = n'⁻¹ n`.
* **Hard direction.** Suppose `n = u n' p`. Put `C' = n · C`, a chamber by
  `normalizer_smul_isChamber` under the apartment axioms. Then
  `u (n' n⁻¹) = n p⁻¹ n⁻¹ ∈ P_{C'}`, by the covariance of the full parahoric under `N(F)`.
  The chamber Iwahori decomposition at `C'` and `-ν` writes this element as `a z b`, with
  `a ∈ U(ν)`, `z ∈ Z(F)^0` and `b ∈ U(-ν)`. Here `U(±ν)` are the dynamic unipotents. The
  reduction uses `-ν`, which is again generic. Then `(n' n⁻¹) z⁻¹` is a product of a point of
  `U(ν)` and a point of `U(-ν)`. The published opposite-unipotent separation
  `normalizer_eq_one_of_unipotent_product` forces this normalizer point to be `1`. Hence
  `n' n⁻¹ = z ∈ Z(F)^0`.

The literal standard unipotent enters only through the inclusion
`standardUnipotentPoints P.i ν ∅ ≤ U(ν)`
(`standardUnipotentPoints_empty_le_dynamic`), which holds because `ν` is a standard
cocharacter for the empty index. No definitional equality between `standardUnipotentPoints`
and `Dynamic.unipotent` is assumed. The Library also proves the two equal, through
`standardUnipotent_empty_eq_dynamic`, but this proof does not need that.

## Hypotheses and scope

The theorem keeps the Henselian and perfect-residue-field hypotheses unchanged. This route
does not use them. The apartment axioms are used to transport chambers by `N(F)` and as a
premise of the chamber Iwahori decomposition. The proof adds no Iwasawa, Iwahori
factorization, normalizer-coset, building-validity or algebraic-comparison premise: the
normality of `Z(F)^0` and the chamber Iwahori products both come from published proofs. The
result is conditional on actual `ParahoricBuildingData` satisfying the fixed-apartment axioms.
It does not construct such data.

This is the authors' replaced Lemma 5.3.5 for the chamber parahoric `P_C`. The printed lemma,
which concerns an arbitrary bounded subgroup containing `Z(k)^0` and elements of `Z(k)`, is
superseded by the corrections and is neither stated nor proved here.

## Provenance

The statement is the replacement of KP Lemma 5.3.5 in the authors' corrections of 1 November
2024 (`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF p. 30). It uses the
notation of KP Theorem 5.3.3 (`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`, book PDF pp. 220–221).

The authors' proof follows the same outline. It translates to `C' = n · C`, writes
`u n' n⁻¹ ∈ P_{C'}` through the Iwahori decomposition
`P_{C'} = (U(k) ∩ P_{C'}) × Z(k)^0 × (U⁻(k) ∩ P_{C'})` (Axiom 4.1.16, which is KP Corollary
7.4.9 for this data). It then concludes `n' n⁻¹ ∈ Z(k)` by the Bruhat decomposition of `G(k)`
with respect to `U(k)Z(k)` and `U⁻(k)Z(k)`, and `n' n⁻¹ ∈ Z(k)^0` by the Iwahori decomposition
again. The implemented route differs in the separation step. It uses the factor order
`U(ν) · Z(F)^0 · U(-ν)` of the chamber decomposition at `-ν`, and replaces the Bruhat
decomposition argument by the Library's opposite-cell separation
`normalizer_eq_one_of_unipotent_product`. That step gives `n' n⁻¹ = z ∈ Z(F)^0` directly.

The companion target `IwasawaDecompositionStatement` of the same task is proved separately by
`Langlands.Geometry.Building.iwasawaDecomposition` (module `IwasawaDecompositionProof`).
