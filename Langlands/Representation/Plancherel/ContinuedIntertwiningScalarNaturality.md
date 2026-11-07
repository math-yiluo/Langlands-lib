# Representative invariance of continued composite scalars

This is a derived construction combining Waldspurger IV.1, printed
pp.276–277 (PDF pp.42–43), and the beginning of IV.3, printed p.285
(PDF p.51), in `waldspurger-2003-plancherel`. It compares two pairs of
independently continued operators related by a fixed isomorphism of
inducing representations at the same character parameter. It constructs
conjugated continuation data and proves invariance of the resulting
function-field coefficient. Under generic scalarity, arbitrary normalized
coefficient choices give the same rational scalar. The final theorem
obtains that scalarity from generic irreducibility of the actual normalized
induction for the first representative.

The source's IV.1 representative square and its fixed compact carriers
motivate the conjugation constructions; IV.3 motivates the scalar
comparison after Schur's lemma. This module derives their compatibility
from the existing continuation, density and compact-induction results.
It does not identify the supplied operators with standard integrals or
construct their convergence and rationality witnesses.

## Generic conjugation data

The first section uses an arbitrary topological group `H`, a family of
positive real characters `ν`, four complex module carriers `V,W,V',W'`
in independent universes, and original families
`A : Ω → V →ₗ[ℂ] W` and `B : Λ → W →ₗ[ℂ] V`.
There are no dimension or vector-space topology assumptions. A datum
`p : RationalOperatorContinuationData Ω A` supplies one whole-operator
regular denominator and a polynomial operator numerator. Write `Rₚ` for
its denominator's nonzero locus.

`RationalOperatorContinuationData.congr p S T`, for linear equivalences
`S : V ≃ₗ[ℂ] V'` and `T : W ≃ₗ[ℂ] W'`, continues the family
`T ∘ A(χ) ∘ S⁻¹`. It is defined by the existing `p.map` with precomposition
by `S⁻¹` and postcomposition by `T`. It retains the exact denominator;
`congr_regularRegion` and `congr_continuedOperator` give its regular region
and continued operator explicitly.

`continuedComposite_congr` cancels the intermediate `T` in the composite
of `p.congr S T` with `q.congr T S`. At every `χ ∈ Rₚ ∩ R_q`, its value on
`S v` equals `S (q_ext(χ) (p_ext(χ) v))`. The proof unfolds the two scalar
multiplications by the inverse denominators and uses linearity and inverse
cancellation. `continuedCompositeScalar_congr` applies the transported
functional `ℓ ∘ S⁻¹` to this identity. It preserves the coefficient for
any `v,ℓ`, without normalization or scalarity.

## Actual character parameters and independent continuations

The remaining character results use all rational norm characters of a
connected reductive group scheme `L` over an arbitrary nonarchimedean
local field `F`. A topology on its actual rational points, continuity `hp`
of `rationalValuationImageProjection L`, and connected reductivity `hL`
are explicit. They are exactly the premises of the imported density and
regular-function uniqueness results. There is no restriction on the
characteristic or splitness of `L`.

`continuedCompositeRationalScalar_congr` identifies the function-field
coefficient before and after conjugation and transport of `v,ℓ`. It needs
nonempty original regions `Ω,Λ` to obtain the nonempty open composite
regular region. It applies
`ScalarPresentation.toFunctionField_eq_of_eqOn_isOpen` to the pointwise
coefficient identity above. Its value lies in the imported
`rationalUnramifiedFunctionField L hp hL`; no evaluation at poles is used.

For independent original families `A',B'` and continuation data `p',q'`,
assume two ambient open nonempty sets

- `D ⊆ Ω ∩ Ω'`, with `A'(χ) ∘ S = T ∘ A(χ)` on `D`;
- `E ⊆ Λ ∩ Λ'`, with `B'(χ) ∘ T = S ∘ B(χ)` on `E`.

The two sets need not intersect, and the four denominators need not be
related. The supplied continuation data make each denominator nonzero
on its own original region. These equations are premises about the
original operators, not conclusions inserted about their continuations.

`continuedComposite_natural` applies
`rationalOperatorContinuationData_natural` once to the forward square on
`D` and once to the reverse square on `E`. Evaluating both operator
identities at vectors and composing proves

`q'_ext(χ) (p'_ext(χ) (S v)) = S (q_ext(χ) (p_ext(χ) v))`

on the intersection of all four regular regions.
`continuedCompositeRationalScalar_natural` compares the fractions there,
using the same transported extraction pair as above. Density of
`R_p' ∩ R_q'` makes its intersection with the nonempty open
`Rₚ ∩ R_q` nonempty. The coefficient equality then identifies the
function-field elements. No scalarity is needed for this comparison.

`continuedCompositeRationalScalar_representative_independent` allows an
arbitrary normalized extraction pair on each source carrier:
`ℓ v = 1` and `m w = 1`. Its additional premise is a nonempty ambient
open set `U` on which the first composite is scalar wherever defined.
There is no premise that `U` avoids any denominator or lies in an
original region. Density makes `U ∩ Rₚ ∩ R_q` nonempty. The proof first
uses `rationalUnramifiedScalarContinuation` to extend the first
composite's scalar identity throughout `Rₚ ∩ R_q`. On the fourfold
regular intersection, the proved composite square and surjectivity of
`S` transfer that same scalar identity to the second composite. Applying
`m` to `w` then gives the same coefficient because `m w = 1`. The
nonempty open comparison theorem identifies the two fractions.

These results allow independent continuation choices for the four fixed
original families and independent normalized extraction pairs. They keep
the specified representative isomorphism and the character parameter
fixed; they do not compare different character parameters.

## Actual normalized-induction specialization

The final section uses a locally compact nonarchimedean group `G`;
semidirect decompositions `Pᵢ = M Uᵢ` with the same literal Levi; closed
`Pᵢ` and `Uᵢ`; the existing `IsUnimodularModulus` hypotheses; a common
compact open subgroup `K` with `G = Pᵢ K`; and continuous Levi projections.
It also supplies a topological group isomorphism
`e : L.rationalPoints ≃ₜ* M` and continuity of every rational norm
character. The parameter `χ` on `L.rationalPoints` is transported to `M`
by `unramifiedCharactersHomeomorph e`; the underlying norm characters
are composed with `e.symm`.

`A` and `B` are canonical complex `Langlands.SmoothRep` objects of `M`,
with independent carrier universes, and
`φ : A.representation.Equiv B.representation` is a fixed intertwining
equivalence. There are four supplied actual ambient intertwiner families:
`J₁₀,J₀₁` for `A` and `J₁₀',J₀₁'` for `B`, on four independent original
regions. Their data `p,q,p',q'` continue exactly their compact conjugates
under `compactIntertwiningOperator`.

Two separate nonempty ambient open subsets `D₁₀,D₀₁` lie in the two
respective pairs of original regions. The premises `hnat₁₀,hnat₀₁`
are the original actual representative squares: the vertical maps are
`inducedMap` of `twistEquiv` of `φ`, and the horizontal maps are the
supplied actual `J` families. Neither intersection of `D₁₀` and `D₀₁`
nor common denominators are required.

`continuedInductionCompositeRationalScalar_representative_independent`
additionally assumes `TopologicalSpace.SeparableSpace G` and a nonempty
ambient open `U` on which the actual normalized induction from `P₀` of
`A ⊗ χ` is irreducible. It requires no irreducibility premise for `B` or
for induction from `P₁`. The two normalized extraction pairs belong to
`CompactInductionPicture h₀ K A` and `CompactInductionPicture h₀ K B`.
The conclusion is equality of their two `continuedCompositeRationalScalar`
values, for the independently supplied pairs of continuation data.

The proof applies the general representative-independence result with the
linear equivalences underlying `compactInductionPictureEquiv` for `P₀`
and `P₁`. The existing `compactIntertwiningOperator_natural` turns each
original actual square into the corresponding compact square. For the
first composite, `continuedInductionComposite_generic_scalar` applies
separable smooth Schur to the continued actual ambient endomorphism at
parameters in `U ∩ Rₚ ∩ R_q` and transports its scalarity to the compact
picture. The general result then completes the rational scalar comparison.
This compares coefficients of the actual continued operators through
the exact compact-composite identity from `ContinuedIntertwiningScalar`.

## Scope and retained obligations

The field, group and inducing-carrier universes are independent. No
admissibility, finite-dimensionality or characteristic-zero premise is
introduced. The ambient subgroup, topology, modulus, compact-factorization
and rational-point identification hypotheses remain displayed; this
construction supplies no general rational-point realization of them.

The rational continuation witnesses, the two original representative
squares and the generic induced-irreducibility premise remain substantive
representation-theoretic obligations. They are not permitted external
structural inputs to the main conditional Plancherel theorem. The original
IV.1 uses admissible orbit-indexed families; this module isolates a fixed
same-parameter representative comparison and proves it with weaker
representation hypotheses. IV.3 uses opposite standard intertwiners;
this result permits arbitrary supplied ambient intertwiner families.

Standard-integral convergence, rationality and original naturality,
generic induced irreducibility, parameter reindexing and stabilizer/orbit
descent, independence of `K` or parabolic, Weyl and contragredient
compatibility, nonvanishing and positivity, the global source-normalized
`j` and `mu`, and the main Plancherel assertions remain separate obligations.
