# Reductions for the Iwahori–Weyl exact sequence and chamber splitting

The setting is the actual building data `P : ParahoricBuildingData G` of a connected reductive
group `G` over a nonarchimedean local field `F`, under the apartment axioms
`P.apartment.SatisfiesApartmentAxioms P.centralizer`. Here `S` is the maximal split torus,
`N = N_G(S)`, `Z = Z_G(S)` and `W̃^0 = N(F)/Z(F)^0`. This module reduces the published targets
`IwahoriWeylExactSequenceStatement` (KP Theorem 7.8.1(1)) and
`IwahoriWeylChamberSplittingStatement` (KP 7.8.2) to source statements. Each source statement
enters as an explicit hypothesis, and none is proved here:

| Hypothesis | Source | Used for |
| --- | --- | --- |
| `UnramifiedZeroPointsIndependenceStatement` | KP Lemma 2.6.24 (independence) | `Z(F)^0 ⊴ N(F)` |
| `SimplyConnectedCentralizerProductStatement` | KP Fact 2.6.22 | `G(F)^0 ⊴ G(F)`; surjectivity onto `G(F)/G(F)^0` |
| `SimplyConnectedNormalizerAffineWeylStatement` | KP Theorem 7.5.3(2) | the image `W(Ψ)` of `N(F) ∩ G(F)^0` |
| `P.zeroDatum.CentralizerZeroIntersectionStatement` | KP Corollary 2.6.28 | the kernel `Z(F)^0` of the action |
| `AffineChamberSimpleTransitivityStatement` | KP Lemma 1.3.17 | chamber splitting |

## Proofs

**Normality of `Z(F)^0` in `N(F)`** (`normalizerZero_normal`). For `n ∈ N(F)`, inner
conjugation by `n` preserves the centralizer subgroup functor of `S`
(`torusCentralizer_comap_innerIso_normalizer`). It therefore restricts to an automorphism
`centralizerConjIso n : Z ≅ Z` (`SubgroupFunctor.IsRepresentedBy.isoOfComap`), with
`j(α z) = n j(z) n⁻¹` (`map_centralizerConjIso`). By `map_mem_anisotropicZeroPoints` (module
`UnramifiedZeroTransport`, which uses the independence hypothesis), `α` preserves
`Z(F)^0 = Z(K)^0 ∩ Z(F)`.

**Normality of `G(F)^0`** (`zeroSubgroup_normal`). Fact 2.6.22 writes `g = c · j(z)` with
`c ∈ G(F)^♮` and `z ∈ Z(F)`. Conjugation by `c ∈ G(F)^0` preserves `G(F)^0`. Conjugation by
`j(z)` preserves `G(F)^♮`, which is normal by the published `simplyConnectedImage_normal`. It
also preserves `j(Z(F)^0)`, since `j(z) ∈ N(F)` and `Z(F)^0 ⊴ N(F)`. The product form
`G(F)^0 = G(F)^♮ · j(Z(F)^0)` is the published `mem_zeroSubgroup_iff`.

**Surjectivity of `W̃^0 → G(F)/G(F)^0`** (`toComponents_surjective`). For `g = c · j(z)` as
above, `g G(F)^0 = j(z) G(F)^0`, because `G(F)^0` is normal and contains `c`. The class of
`j(z) ∈ N(F)` therefore maps to `g G(F)^0`, which is the criterion
`toComponents_surjective_iff`.

**Image of the action** (`normalizerAffineEquiv_mem_affineWeylGroup`,
`exists_normalizerZeroComponent_normalizerAffineEquiv_eq`). Write `n ∈ N(F) ∩ G(F)^0` as
`n = c · j(y)` with `c ∈ G(F)^♮` and `y ∈ Z(F)^0`. Then `c = n · j(y)⁻¹ ∈ N(F) ∩ G(F)^♮`, and
`j(y)` acts trivially, since `Z(F)^0 ⊆ Z(F)^1` and `Z(F)^1` acts trivially by axiom V 6. So
`n` acts as `c`, which lies in `W(Ψ)` by Theorem 7.5.3(2). Conversely, every element of
`W(Ψ)` is the action of some `c ∈ N(F) ∩ G(F)^♮ ⊆ N(F) ∩ G(F)^0`.

**Kernel of the action** (`normalizerAffineEquiv_eq_one_iff`). Elements of `Z(F)^0` act
trivially (`normalizerAffineEquiv_eq_one_of_mem_normalizerZero`). Conversely, suppose
`n ∈ N(F) ∩ G(F)^0` acts trivially.

1. The linear part `translationAction n` of the action is trivial. Hence for every root `α`
   and real cocharacter `v`, `α(n·v) = α(v)`, so `n⁻¹` fixes every relative root. The roots
   and the restrictions of the rational characters of `G` span the rational character space
   (`relativeRootsRestrictedCharactersSpan`), and the Weyl action fixes restricted
   characters. So the Weyl action of `n` is trivial
   (`IsSplitTorus.weylAction_eq_one_of_fixed_roots`), and `n` centralizes `S`
   (`IsSplitTorus.weylAction_eq_one_iff`). Hence `n = j(z)` for some `z ∈ Z(F)`.
2. By V 6, `j(z)` acts as translation by the class of `ν(z)`. That translation is trivial, so
   every root vanishes on `ν(z)`.
3. `j(z) ∈ G(F)^0 ⊆ G(F)^1` (published `zeroSubgroup_le_rationalCommonNormKernel`). Hence the
   restriction to `S` of every rational character of `G` vanishes on `ν(z)`
   (`eval_torusCharacterRestrict_translation`).
4. By the spanning statement again, every character of `S` vanishes on `ν(z)`. The argument
   extends `β ↦ β(ν(z))` to a `ℚ`-linear map with `LinearMap.liftBaseChange`. By the defining
   property `centralizerValuation_spec` of `ν`, every rational character of `Z` has valuation
   `0` at `z`, so `z ∈ Z(F)^1`.
5. Corollary 2.6.28, `G(F)^0 ∩ Z(F)^1 = Z(F)^0` on `Z(F)`, gives `z ∈ Z(F)^0`.

**Assembly.** `iwahoriWeylExactSequence_of_prerequisites` feeds the three action properties
into the published `exists_affinePart_equiv_of_action`. It also uses the published
`toComponents_ker_eq_affinePart` and the surjectivity above.
`iwahoriWeylExactSequenceStatement_of_prerequisites` is the same for all `F`, `G` and `P`.
`iwahoriWeylChamberSplittingStatement_of_exactSequence` applies the published
`iwahoriWeylChamberReduction` with simple transitivity on chambers for `Ψ = P.affineRoots`,
which is an affine root system by axiom AS 3.

## Provenance

The reductions follow the proofs of KP Lemma 2.6.24, Lemma 7.5.2, Theorem 7.5.3, Theorem
7.8.1(1) and 7.8.2 (printed pp.104–106, 260–261, 272–273/PDF pp.135–137, 291–292,
303–304). For the surjectivity onto `G(F)/G(F)^0`, KP cites Fact 4.1.25; here it is derived
from Fact 2.6.22 instead. The kernel
argument uses the faithfulness of the relative Weyl group on `V(S)/V(S)^Φ` and the description
of `Z(F)^1` as the kernel of `ν`, as in the proof of Theorem 7.8.1(1). The definition
`centralizerConjIso` is internal: it is the restriction of `Int(n)` to `Z_G(S)` used in the
proof of Lemma 2.6.24. The theorems prove only the stated implications; the hypotheses are
separate statements.

Source: Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023)
(`kaletha-prasad-2023-bruhat-tits-new-approach`), with the 2024 corrections
(`kaletha-prasad-2024-corrections`).
