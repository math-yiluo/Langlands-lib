# Proof: the oriented split center of Harris's CM composite

`harrisCMCompositeSplitCenter` proves
`HarrisCMCompositeSplitCenterStatement.{u}`, defined in the module
`Langlands.Shimura.Unitary.HarrisCMCompositeSplitCenterStatement`, for every
universe `u`. Let `E` be a CM
number field with intermediate fields `E₀` and `K₀` over `ℚ`, `E₀` totally real
and `E₀ ⊔ K₀ = ⊤`. Let `v` be a finite place of `E` whose residue characteristic
satisfies `Harris.IsSplitImaginaryQuadratic` for `K₀`: `K₀` is imaginary
quadratic and this rational prime splits in it. The proof supplies the
witnesses in the order the statement fixes them. The place below `v` is
`w = v.under (𝓞 E₀)` and the second place is `Harris.conjPlace E v`. The two
coordinates are `completedCenterMap E₀ E w v` and
`completedCenterMap E₀ E w (Harris.conjPlace E v)`, in that order. No hypothesis
is added to the statement.

## The quadratic extension

`isQuadraticExtension_of_sup_eq_top` proves `[E : E₀] = 2`. The first conjunct
of `IsSplitImaginaryQuadratic` gives `[K₀ : ℚ] = 2`. Mathlib's compositum bound
`IntermediateField.finrank_sup_le` with `E₀ ⊔ K₀ = ⊤` gives
`[E : ℚ] ≤ 2 [E₀ : ℚ]`, and the tower law gives `[E : E₀] ≤ 2`. The degree is
positive. If it were `1`, then `E₀ = ⊤` by
`IntermediateField.finrank_eq_one_iff_eq_top`.
`complexConj_eq_self_of_isTotallyReal` shows that complex conjugation of `E`
fixes every element of a totally real intermediate field. Such a field lies in
the maximal real subfield (`IsTotallyReal.le_maximalRealSubfield`), whose
elements conjugation fixes (`IsCMField.complexConj_eq_self_iff`). Conjugation
would then be the identity, contradicting `IsCMField.complexConj_ne_one`.

## The two places above `w`

`v` lies over `w` because `w.asIdeal` is by definition the contraction of
`v.asIdeal`. `conjPlace_liesOver_of_isTotallyReal` proves that
`Harris.conjPlace E v` lies over every place of `E₀` that `v` lies over. The
conjugate ideal is the preimage of `v.asIdeal` under the automorphism of `𝓞 E`
induced by complex conjugation, and this automorphism fixes the image of `𝓞 E₀`.

Put `p = residueCharacteristic v`. It is prime by `CharP.prime_ringChar`, since
the residue ring is a finite field. Its cast lies in `v.asIdeal` because it
vanishes in the residue field (`CharP.cast_eq_zero`). The theorem
`Langlands.Global.Harris.splitPlaceNeConjPlace` proves
`SplitPlaceNeConjPlaceStatement`. With the splitting hypothesis it gives
`v ≠ Harris.conjPlace E v`.

`placesAbove_eq_or_eq_of_finrank_eq_two` holds for any extension `L/K` of
number fields of degree two. Two distinct places `a` and `b` above a finite place
`p` of `K` are all the places above `p`, and both local degrees are one. The
Library theorem `finiteLocalDegree_sum_le` bounds the sum of the local degrees over
`FinitePlacesAbove L p` by `[L : K] = 2`. Every local degree is positive, so a
third place would make the sum at least `3`, and the degrees at `a` and `b` are
both `1`. Applied to `v` and `Harris.conjPlace E v`, this gives the exhaustion
conjunct of the statement.

## The completion isomorphisms

The `(E₀)_w`-algebra structures on the completions of `E` are the scoped
`FiniteExtension` structures, given by the completion maps
`FiniteExtension.completionMap`. `e₁` and `e₂` are these structure maps at `v`
and at `Harris.conjPlace E v`. Each is an algebra isomorphism by
`Algebra.finrank_eq_one_iff_bijective_algebraMap`, since its local degree is
one.

## The split-center identification

`exists_splitPlaceIdentification` takes a totally real `E₀ ⊆ E` with `E/E₀`
quadratic, a place `w` of `E₀`, and a place `v` of `E` such that `v` and
`Harris.conjPlace E v` are distinct and both lie over `w`. It returns
`C : SplitPlaceIdentification E₀ E w`, `e₁` and `e₂` with the exhaustion and the
two coordinate identities.

The map `C.equiv` is the `(E₀)_w`-algebra map
`z ↦ (e₁⁻¹ (completedCenterMap E₀ E w v z), e₂⁻¹ (completedCenterMap E₀ E w (conjPlace E v) z))`
from `LocalCenter E₀ E w = (E₀)_w ⊗[E₀] E` to `(E₀)_w × (E₀)_w`. The coordinate
identities of the statement hold by construction:
`e₁ (C.equiv z).1 = completedCenterMap E₀ E w v z`, and likewise for `e₂`.

This map is injective. `completedCenterMap_eq_finiteTensorMap_of_liesOver`
identifies `completedCenterMap E₀ E w q` with the `q` coordinate of
`finiteTensorMap`. Every place above `w` is `v` or
`Harris.conjPlace E v`, so an element with both coordinates zero is sent to zero
by `finiteTensorMap`. That map is bijective by
`completedTensorComparison`. Both sides have dimension two over `(E₀)_w`
(`Module.finrank_baseChange` and `IsQuadraticExtension.finrank_eq_two`), so the
injective map is bijective. It is an algebra isomorphism by
`AlgEquiv.ofBijective`.

## Conjugation exchanges the coordinates

`conjCompletionEquiv v` is `finiteCompletionEquiv` for complex
conjugation `c`. It is the ring isomorphism from the completion at
`Harris.conjPlace E v` to the completion at `v` that extends `c` on `E`
(`conjCompletionEquiv_algebraMap`). `conjCompletionEquiv_completionMap` shows
that it intertwines the completion maps from `(E₀)_w`. Both composites are
continuous, and they agree on the dense image of `E₀` because `c` fixes `E₀`.
On simple tensors `s ⊗ k` this gives `conjCompletionEquiv_completedCenterMap`:
the transport of the coordinate of `z` at `Harris.conjPlace E v` is the
coordinate at `v` of `localConjugation E₀ E w z`. The conjugation on simple
tensors is `s ⊗ k ↦ s ⊗ c(k)` by `localConjugation_tmul`.

The intertwining gives `conjCompletionEquiv v ∘ e₂ = e₁`. Hence
`e₁⁻¹ (conjCompletionEquiv v y) = e₂⁻¹ y` for every `y` in the completion at
`Harris.conjPlace E v`. So the first coordinate of `C.equiv` at the conjugate of
`z` is the second coordinate at `z`. Applying this to the conjugate of `z` and
using that `localConjugation` is an involution gives the other coordinate. This
is the field `conjugation_eq` of `SplitPlaceIdentification`.

## Assembly

`harrisCMCompositeSplitCenter_of_splitPlaceNeConjPlace` derives the statement
from `SplitPlaceNeConjPlaceStatement.{u}`. It uses the quadratic extension, the
two lying-over facts, the residue characteristic and
`exists_splitPlaceIdentification`. `harrisCMCompositeSplitCenter` applies it to
`Langlands.Global.Harris.splitPlaceNeConjPlace`.

## Relation to other Library results

`SplitCompletionChart` starts from a given `SplitPlaceIdentification`. It proves
local degree one at both upper places and reorients the chart so that a chosen
upper place gives the first coordinate. The present proof constructs the
identification itself, so it obtains local degree one from the degree bound and
distinctness, before any chart exists.
`SplitPlaceIdentification.placesEquivFinTwo` in `SplitPlaceFactors` counts the
places above a split place from a chart. Here the count comes before the chart.

## Provenance

The statement is the derived comparison between Harris, *The local Langlands
conjecture for GL(n) over a p-adic field, n < p* (1998), §1, Theorem 1.2(i)–(ii)
and the splitting hypothesis that follows it, p. 185, and the prescribed
split-place input of Clozel, *Représentations
galoisiennes associées aux représentations automorphes autoduales de GL(n)*
(1991), §2, Proposition 2.3(i)–(ii), pp. 105–106. In Harris, clause (i)
supplies the chosen place and its rational prime, clause (ii) supplies the
compositum of the totally real field with an imaginary quadratic field, and the
hypothesis after the theorem asks that this prime split in the imaginary
quadratic field. The proof is an internal
argument from the completed tensor comparison, the local degree
bound, the completion transport along field isomorphisms, and the distinctness
of a split place from its CM conjugate. It does not follow a proof in these
sources.
