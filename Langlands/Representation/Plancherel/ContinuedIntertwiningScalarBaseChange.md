# Composite scalars after a change of base representation

## Source and provenance

This is a derived construction using Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, IV.1, printed
pp.276–278 (PDF pp.42–44), and the beginning of IV.3, printed p.285
(PDF p.51). The registered source is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

IV.1 defines the unramified twist orbit, fixes compact section carriers
independently of the character, requires naturality under actual
representation isomorphisms, and continues rational operators using a
single denominator for the whole operator. IV.3 obtains a rational
composition scalar by Schur's lemma on a nonempty generic irreducibility
locus. This module combines those conventions with the existing parameter
translation, independent-continuation and scalar-extraction results. It
proves how the extracted scalar transforms when the base representation
changes by an unramified twist. It is not a separately numbered result
of the source.

## Combined translation and carrier change

The first section uses a group `H` with a topology, a family `ν` of positive
real characters, and four complex module carriers `V,W,V',W'` in independent
universes. No dimension or carrier-topology assumptions are used. Let
`X = unramifiedCharacters ν`, let `tτ(χ) = τ * χ`, and let
`A : Ω → V →ₗ[ℂ] W` and `B : Λ → W →ₗ[ℂ] V` be original families.
Write `Rₚ` for `p.regularRegion` when
`p : RationalOperatorContinuationData Ω A`.

For linear equivalences `S : V ≃ₗ[ℂ] V'` and `T : W ≃ₗ[ℂ] W'`,
`RationalOperatorContinuationData.baseChange p τ S T` is defined as
`(p.translation τ).congr S T`. It continues

`χ ↦ T ∘ A(τ * χ) ∘ S⁻¹`

on `tτ ⁻¹' Ω`. Translation pulls back the chosen denominator and
polynomial numerator; conjugation retains that denominator. Thus its
whole-operator denominator is exactly `χ ↦ bₚ(τ * χ)`, and
`baseChange_regularRegion` gives `tτ ⁻¹' Rₚ`. The theorem
`baseChange_continuedOperator` identifies the continued operator with
`T ∘ p_ext(τ * χ) ∘ S⁻¹` on precisely this region.

The composite convention is `q_ext(χ) ∘ p_ext(χ)`. The theorem
`translation_continuedComposite` identifies the composite of the
translated data with the original composite at `τ * χ`; this equality
is definitional. The theorem `baseChange_continuedComposite` gives

`q_base_ext(χ) (p_base_ext(χ) (S v)) = S (q_ext(τ * χ) (p_ext(τ * χ) v))`.

Its domain is the intersection of the two exact pulled-back regular
regions. Its proof uses the imported composite-conjugation identity:
the intermediate `T` and `T⁻¹` cancel.

## Function-field translation

The remaining character results take `X` to be the actual unramified
character space built from all rational norm characters of `L(F)`.
Here `F` is an arbitrary nonarchimedean local field and `L` is a group
scheme over `F`, with a supplied topology on its actual rational points,
continuous rational valuation-image projection `hp`, and connected
reductivity `hL`. These hypotheses support the imported density and
regular-function uniqueness results. There is no splitness or
characteristic-zero restriction.

Write `c(p,q;v,ℓ)` for `continuedCompositeRationalScalar L hp hL p q ... v ℓ`.
It is the element of `rationalUnramifiedFunctionField L hp hL` extracted
from the coefficient `ℓ (q_ext(χ) (p_ext(χ) v))` on `Rₚ ∩ R_q`.
It is defined for arbitrary `v,ℓ`; scalarity and `ℓ v = 1` are not
needed to form this coefficient fraction.

`continuedCompositeRationalScalar_translation` proves

`c(p.translation τ,q.translation τ;v,ℓ) = tτ* c(p,q;v,ℓ)`,

where `tτ*` is `rationalUnramifiedFunctionFieldTranslation L hp hL τ`.
The theorem explicitly takes nonemptiness of `Ω,Λ` and their translated
preimages, so the imported nonempty composite-region results apply.
It uses `rationalUnramifiedOperatorScalar_translation` on the rational
composite. The translated and original composites are definitionally
related as above.

`continuedCompositeRationalScalar_baseChange` combines this identity
with coefficient invariance under conjugation. It gives the same
translated fraction for the constructed pair
`p.baseChange τ S T`, `q.baseChange τ T S`, using the extraction pair
`S v, ℓ ∘ S⁻¹`. Its proof composes
`continuedCompositeRationalScalar_congr` with the translation theorem.
Neither theorem assumes scalarity or normalizes the extraction pair.

## Four independent continuations

Now supply independent families `A' : Ω' → V' →ₗ[ℂ] W'` and
`B' : Λ' → W' →ₗ[ℂ] V'`, with continuation data `p',q'`.
Assume two nonempty ambient open sets and original squares:

- `D ⊆ tτ ⁻¹' Ω ∩ Ω'`, with `A'(χ) ∘ S = T ∘ A(τ * χ)` on `D`;
- `E ⊆ tτ ⁻¹' Λ ∩ Λ'`, with `B'(χ) ∘ T = S ∘ B(τ * χ)` on `E`.

The opens are for the topology of the actual character space; there is
no requirement that they intersect. All four denominators are independent.
The displayed equations concern the original families. No continued
comparison or scalar conclusion is assumed in them. Nonemptiness of
the original `Ω,Λ` follows from the images `tτ '' D,tτ '' E`; that of
their pulled-back regions and the new original regions follows directly
from `D,E`.

`continuedComposite_translation_natural` proves the composite square at
every parameter in

`tτ ⁻¹' (Rₚ ∩ R_q) ∩ (R_p' ∩ R_q')`.

It applies `continuedComposite_natural` to `p.translation τ`,
`q.translation τ`, `p'`, and `q'`. That imported result continues the
two original squares separately before composing them.

`continuedCompositeRationalScalar_translation_natural` then proves

`c(p',q';S v,ℓ ∘ S⁻¹) = tτ* c(p,q;v,ℓ)`.

It composes the imported naturality comparison of coefficient fractions
with `continuedCompositeRationalScalar_translation`. It still needs
neither scalarity nor normalization.

`continuedCompositeRationalScalar_base_independent` permits arbitrary
extraction pairs on the two source carriers, with `ℓ v = 1` and
`m w = 1`. Its additional premise is a nonempty ambient open `U` on
which `p.continuedComposite q` is scalar wherever defined. It does not
require `U` to lie in an original region or avoid any denominator.
Its conclusion is

`c(p',q';w,m) = tτ* c(p,q;v,ℓ)`.

The proof uses that `tτ` is a homeomorphism: `tτ ⁻¹' U` is open and
nonempty, and the scalarity premise pulls back to the translated
composite. It applies
`continuedCompositeRationalScalar_representative_independent` to the
translated first pair and the independent second pair, then identifies
the first fraction by the translation theorem. The imported result
uses density to obtain the required nonempty regular intersections,
extends generic scalarity by rational uniqueness, and removes the
choice of normalized extraction pair. All equalities here are in the
function field; they introduce no evaluation at poles.

## Actual normalized induction

The final section specializes to canonical complex `Langlands.SmoothRep`
objects `A,B` of an actual subgroup `M` of `G`, with independent carrier
universes. The explicit ambient hypotheses are:

- a locally compact nonarchimedean topological group `G`;
- semidirect decompositions `P₀ = M U₀`, `P₁ = M U₁`, closed `Pᵢ,Uᵢ`,
  and the supplied `IsUnimodularModulus` premises for `Uᵢ`;
- a common compact open subgroup `K`, factorizations `G = Pᵢ K`,
  and continuous Levi projections;
- a topological group isomorphism `e : L.rationalPoints ≃ₜ* M`
  and continuity of every rational norm character.

The field and group-scheme hypotheses from the actual-character section
remain explicit. The theorem adds separability of `G`. None of these
premises is asserted to be realized for every reductive rational-point
group by this module.

Write `χM` for `unramifiedCharactersHomeomorph e` and `νM` for the
transported norm characters. Fix a representation equivalence
`a : A.twist (χM τ) ≃ B`. The supplied ambient intertwiner families
`J₁₀,J₀₁` for `A` and `J₁₀',J₀₁'` for `B` have four independent
original regions. Their data `p,q,p',q'` continue exactly their
`compactIntertwiningOperator` conjugates.

There are two nonempty ambient open comparison sets `D₁₀,D₀₁` with the
translated containments above. The premises `hnat₁₀,hnat₀₁` are actual
ambient squares whose vertical maps are `inducedMap` of
`transportedBaseTwistEquiv e ... τ χ a`. This equivalence identifies
the `A` action at `χM (τ * χ)` with the `B` action at `χM χ` and has
the original vector map `a`. These squares are assumed only on their
respective original comparison sets, which may be disjoint.

`continuedInductionCompositeRationalScalar_base_independent` assumes
that the actual normalized induction from `P₀` of `A ⊗ χM χ` is
irreducible on one nonempty ambient open `U`. It requires irreducibility
neither for `B` nor for induction from `P₁`. For arbitrary normalized
extraction pairs on `CompactInductionPicture h₀ K A` and
`CompactInductionPicture h₀ K B`, it proves the function-field
translation equality just displayed.

The proof applies the general base-independence theorem with the fixed
linear equivalences underlying `compactInductionBaseChangeEquiv` for
`P₀,P₁`. The imported
`compactIntertwiningOperator_transportedBaseChange_iff` converts each
original ambient square into its compact square. Finally,
`continuedInductionComposite_generic_scalar` derives the first
composite's scalarity from separable smooth Schur and the supplied
irreducibility on `U`. Its original open regions are the translated
images `tτ '' D₁₀` and `tτ '' D₀₁`; their openness and nonemptiness
follow from the translation homeomorphism. The general result completes
the comparison. The imported actual-compact composite identity identifies
these fractions as coefficients of the actual continued ambient
endomorphisms.

## Scope and remaining obligations

The field, ambient-group and representation-carrier universes remain
independent. No admissibility or finite-dimensionality premise is added.
The construction works for arbitrary supplied intertwiner families;
`P₀,P₁` need not be opposite in this theorem.

Rational continuation witnesses, original ambient base-change squares,
and generic induced irreducibility remain substantive representation
proof obligations. They are not external structural inputs permitted
by the main Plancherel task. The source's standard-integral convergence,
rationality and original squares are not proved here.

This module proves a change-of-chart identity for extracted scalars.
It does not construct a function on the representation orbit or establish
stabilizer invariance for standard operators. The ordinary compact maps
still depend on the chosen equivalence `a`. Standard-operator
identification, independence of `K` or parabolic, Weyl and contragredient
compatibility, nonvanishing, positivity, the global source-normalized
`j` and `mu`, and the main Plancherel assertions remain separate obligations.
