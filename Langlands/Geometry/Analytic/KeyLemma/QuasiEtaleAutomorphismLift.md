# Lifts of near-identity automorphisms to compact quasi-étale spaces

This module proves `quasiEtaleAutomorphismLift`, a proof of the Library
statement `QuasiEtaleAutomorphismLiftStatement`. That statement is the
existence half of Key Lemma 7.2 of Berkovich, *Vanishing cycles for
formal schemes* (Invent. Math. 115, 1994), for near-identity
automorphisms. Let `f : U ⟶ X` be a quasi-étale morphism of analytic
spaces with `U` compact Hausdorff, and let `E` be a finite set of test
triples on `U`. Then there is a finite set `D` of test triples on `X`
such that every automorphism `σ` of `X` that is `D`-near the identity
is covered by an endomorphism `ψ` of `U`. Covered means `ψ ≫ f = f ≫ σ`,
and `ψ` is `E`-near the identity.

The proof derives this from the module `QuasiEtaleStrongNearLifts`, which
gives near lifts at the level of strong maps. Two further steps are
needed: passing from strong maps to the localized category, and
transporting test triples along the isomorphisms that present `f` by a
strong map.

## Transport of tests along isomorphisms

`exists_isNear_iso_postcomp` takes an isomorphism `e : V ≅ W` in the
localized category and a finite set `E` of test triples on `W`. It gives
a finite set `F` of test triples on `V` with the following property: if
two morphisms `φ ψ : Z ⟶ V` are `τ`-near for every `τ` in `F`, then
`φ ≫ e.hom` and `ψ ≫ e.hom` are `τ`-near for every `τ` in `E`.

For each test triple `τ` in `E`, the Library lemma
`exists_isNear_postcomp` gives a finite set of test triples on `V`.
That lemma needs the preimage of the locus of `τ` under `e.hom` to be
compact. The locus of `τ` is compact (`TestTriple.isCompact_locus`), and
`e` induces a homeomorphism of the underlying spaces, so the preimage is
compact. `F` is the union of these finitely many sets.

## From strong lifts to lifts in the localized category

`exists_nearLift_of_hasStrongNearLifts` takes a strong map `g : T ⟶ B`
of saturated atlas presentations with `HasStrongNearLifts g`, and a
finite set `E` of test triples on `T`. Let `D` be the set of test
triples on `B` that `HasStrongNearLifts g` gives for `E`. The theorem
states that every endomorphism `σ` of the localization of `B` that is
`D`-near the identity is covered by an endomorphism `ψ` of the
localization of `T`, with `ψ ≫ g = g ≫ σ` and `ψ` `E`-near the identity.
Here `g` also denotes its image in the localized category.

1. Precomposing with `g` (`IsNear.precomp`) shows that `g` and `g ≫ σ`
   are `D`-near, and that `g` is `D`-near itself.
2. The Library lemma `exists_strongNear_numerators` represents `g`,
   `g ≫ σ` and `g` on a common source. It gives a quasi-isomorphism
   `t : S ⟶ T` and strong maps `x₀`, `x₁` and `x₂` from `S` to `B` whose
   images are `t` composed with `g`, with `g ≫ σ` and with `g`. It also
   gives `StrongNear τ x₀ x₁` for every `τ` in `D`. The images of `x₀` and
   of `t ≫ g` agree, and the localization functor is injective on maps
   between saturated presentations (`localizationFunctor_map_injective`),
   so `x₀ = t ≫ g`.
3. `HasStrongNearLifts g`, applied to `x = t` and `y = x₁`, gives a
   quasi-isomorphism `r : S' ⟶ S` and a strong map `x' : S' ⟶ T` with
   `x' ≫ g = r ≫ x₁`. It also gives `StrongNear τ x' (r ≫ t)` for every
   `τ` in `E`.
4. The composite `r ≫ t` is a quasi-isomorphism, so it becomes
   invertible in the localized category (`localizedQuasiIso`). Put
   `ψ = (r ≫ t)⁻¹ ≫ x'`. Then `ψ ≫ g = (r ≫ t)⁻¹ ≫ (r ≫ t) ≫ g ≫ σ =
   g ≫ σ`.
5. `ψ` and the identity are right fractions with the common denominator
   `r ≫ t` and the numerators `x'` and `r ≫ t`. So `IsNear τ ψ 𝟙` holds
   for `τ` in `E`, directly from the definition of `IsNear` and step 3.

## The main theorem

`quasiEtaleAutomorphismLift` proves the statement. Since `f` is
quasi-étale, there are affinoid atlas presentations `A` and `B`, a
quasi-étale strong map `g` between their saturations, and an
isomorphism of arrows `e` between the image of `g` and `f`. The
isomorphism `e` consists of isomorphisms `eL` from the localization of
the saturation of `A` to `U`, and `eR` from that of `B` to `X`, with
`eL ≫ f = g ≫ eR` (`Arrow.w`).

The space of `A` is homeomorphic to that of `U` through `eL`, so it is
compact and Hausdorff. Hence `g` has strong near lifts
(`IsQuasiEtale.hasStrongNearLifts`). Given `E` on `U`:

- `exists_isNear_iso_postcomp` for `eL` gives test triples `EA` on `A`;
- `exists_nearLift_of_hasStrongNearLifts` for `g` and `EA` gives test
  triples `DB` on `B`;
- `exists_isNear_iso_postcomp` for `eR⁻¹` and `DB` gives the required
  set `D` on `X`.

Let `σ` be an automorphism of `X` that is `D`-near the identity. Then
`σ ≫ eR⁻¹` and `eR⁻¹` are `DB`-near. Precomposing with `eR` shows that
`eR ≫ σ ≫ eR⁻¹` is `DB`-near the identity. The previous section gives an
endomorphism `ψ₀` of the localization of `A` with
`ψ₀ ≫ g = g ≫ eR ≫ σ ≫ eR⁻¹` and `ψ₀` `EA`-near the identity. Put
`ψ = eL⁻¹ ≫ ψ₀ ≫ eL`. Then `ψ ≫ f = f ≫ σ` follows from `eL ≫ f = g ≫ eR`.
By the choice of `EA`, `ψ₀ ≫ eL` and `eL` are `E`-near. Precomposing
with `eL⁻¹` shows that `ψ` is `E`-near the identity.

The statement also assumes that `X` is Hausdorff. This proof does not
use that hypothesis.
