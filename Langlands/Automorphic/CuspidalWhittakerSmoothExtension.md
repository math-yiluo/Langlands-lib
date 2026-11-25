# Continuous extensions of actual finite-level Whittaker functionals

This module states and proves a conditional existence result: an actual
cuspidal Whittaker evaluation at a fixed finite level extends to a continuous
complex-linear functional on all genuine smooth vectors of a supplied bounded
representation of a real Lie group, along a supplied injective embedding into
those smooth vectors. The representation, the embedding, equality with the
actual determinant-band norm and real-generator compatibility are inputs; none
of them is constructed here.

## The generic Hahn--Banach lemma

`exists_extension_along_smoothEmbedding` works for a real Lie group `G`
(`LieGroup I ∞ G` for a model `I` on a real normed space `𝔤`), a representation
`π : G →* (E →L[ℂ] E)` by bounded operators on a complex normed space `E`, and
a complex vector space `V` with an injective complex-linear map
`j : V →ₗ[ℂ] smoothVectors I π` into the genuine smooth vectors (vectors with
real `C^∞` orbit maps). Suppose a complex-linear `ℓ : V →ₗ[ℂ] ℂ` satisfies, for
a given finite set `S` of words in `𝔤` and a given constant `C ≥ 0`,

`‖ℓ v‖ ≤ C * ∑ Xs ∈ S, ‖iteratedLieDerivative I π Xs (j v)‖` for every `v`.

Then there is a complex-linear `L` on `smoothVectors I π` with `L (j v) = ℓ v`
for all `v`, the same bound with the same `S` and `C` for every smooth vector,
and `IsContinuousOnSmoothVectors I π L`. The proof identifies `V` with the range
of `j` via `LinearEquiv.ofInjective`, transports `ℓ` to a functional on that
submodule (the bound transports unchanged), and applies the published
`exists_extension_of_word_bound`, the complex Hahn--Banach extension dominated
by the seminorm `C • ∑ Xs ∈ S, wordSeminorm I π Xs`. Only existence is
asserted.

## The statement

`CuspidalWhittakerSmoothExtensionStatement F T hL2 ψ I π j ζ` is a Prop-valued
definition. Its parameters are: a number field `F` (with the instance
`CompactSpace (AdeleQuotient F)` required by the published Whittaker and band
definitions); any `r : ℕ`, including `r = 0`, with the group `GL_{r+1}`; an
actual cuspidal operator realization `T : CuspidalOperatorRealization F r`; the
actual determinant-band integrability witness `hL2` (every original vector's
determinant-slice quotient function is in `L²` for the quotient Haar measure
restricted to the determinant band); an additive character `ψ` of the adeles; a
model `I`, a group `G` with `LieGroup I ∞ G`, a complex normed space `E` with
a representation `π` by bounded operators; a complex-linear map
`j : T.Space →ₗ[ℂ] smoothVectors I π`; and a map `ζ` from the actual real Lie
algebra `ArchimedeanGL.RealLieAlgebra F (r + 1)` (square matrices of size
`r + 1` over the archimedean mixed space of `F`) to the model space `𝔤`.

The proposition assumes, in this order:

1. `ψ` is a standard additive character (`IsStandardAdditiveCharacter F ψ`);
2. the band-bound premise `CuspidalWhittakerBandBound F T hL2 ψ`;
3. `j` is injective;
4. for every original vector `v`, the norm of its determinant-band `L²` class
   (`OperatorDeterminantSlice.toL2` for the quotient Haar measure) equals the
   norm of `j v` in `E`;
5. real-generator compatibility: for every real Lie algebra element `X` and
   original vector `v`, `j` sends the actual enveloping action of the generator
   of the complexification of `X` on `v` to the genuine orbit derivative
   `lieDerivative I π (ζ X) (j v)`.

Then for every subgroup `J` of the finite-adelic `GL_{r+1}` that is open and
compact and every compact set `Q` of adelic points, there are a finite set `S`
of genuine derivative words and a constant `C ≥ 0`, chosen before the point,
such that for every `g ∈ Q` there is a complex-linear functional `L` on all of
`smoothVectors I π` with:

- `L (j v) = cuspWhittaker F T ψ v g` for every original vector `v` fixed by
  every element of `J` under the finite-adelic action of `T`;
- `‖L w‖ ≤ C * ∑ Xs ∈ S, ‖iteratedLieDerivative I π Xs w‖` for every smooth
  vector `w`;
- `IsContinuousOnSmoothVectors I π L`.

The universe parameters of the number field, the carrier `E`, the model space
`𝔤`, the model `H` and the group `G` are independent and free.

## The proof

`exists_cuspWhittaker_smoothExtensions_of_bandBound` proves the statement for
all its parameters. It composes three published results.

1. **Word estimate.** With `j₀` the composite of `j` with the inclusion of
   smooth vectors into `E`, `cuspWhittaker_smoothBound_of_bandBound` turns the
   band bound, the norm equality and real-generator compatibility into one
   finite set `S` and one constant `C ≥ 0` (for the given `J` and `Q`) bounding
   `‖cuspWhittaker F T ψ v g‖` by `C * ∑ Xs ∈ S, ‖iteratedLieDerivative I π Xs (j v)‖`
   for every `J`-fixed original `v` and every `g ∈ Q`. These `S` and `C` are the
   ones returned, before the point is chosen.
2. **Fixed-vector restriction and Whittaker linearity.** Fix `g ∈ Q`. Let `V` be
   `fixedVectors T.realization.finiteRepresentation J`, the submodule of
   original vectors invariant under every element of `J`. The functional is
   the published complex-linear map `UnramifiedWhittaker.whittakerFunctional F ψ hψ T g`
   (`v ↦ cuspWhittaker F T ψ v g`; its additivity uses the standard character
   hypothesis), restricted to `V`. The embedding restricted to `V` is still
   injective, and the word estimate of step 1 is exactly the bound required
   on `V`.
3. **Finite-word Hahn--Banach extension.** `exists_extension_along_smoothEmbedding`
   applied to the restricted embedding and functional gives `L` with the same
   `S` and `C` and the continuity predicate. A `J`-fixed original vector is an
   element of `V`, so `L (j v)` is its Whittaker value at `g`.

## Continuity

`IsContinuousOnSmoothVectors I π L` is the published finite-word continuity
predicate. By the published `continuous_iff_isContinuousOnSmoothVectors`, it is
equivalent to continuity of `L` on `DerivativeSmoothVectors I π`, the copy of
the smooth vectors carrying the genuine derivative topology (the topology
induced by all iterated orbit derivatives in the norm of `E`). So each extension
is continuous for the genuine derivative topology. This equivalence is
explained here and not restated in this module.

## Scope and provenance

The result asserts existence only. It claims no density of the image of `j`,
no uniqueness of the extension, no equivariance, no compatibility of the
extensions between different levels `J` or points `g`, and no unconditional
multiplicity-one theorem. In particular it does not show that an extension is
a Whittaker functional on the smooth vectors. The band bound, the
representation, the embedding and both comparison hypotheses remain
assumptions.

The provenance is internal: a composition of the published band-to-word
estimate, actual Whittaker linearity and finite-word Hahn--Banach extension,
prepared for the analytic comparison of Whittaker functions in the proof of multiplicity one
for cuspidal operator realizations (`CuspidalOperatorMultiplicityOneStatement`). No literature statement is
translated.
