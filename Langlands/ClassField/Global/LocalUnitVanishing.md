# Vanishing of the second cohomology of valuation units at unramified places

Let `E / F` be a Galois extension of number fields, `v` a finite place of
`F`, and `w` a finite place of `E` over `v`. Assume that the ramification
index of `w` over `v` is `1`, in the form
`w.asIdeal.ramificationIdx (𝓞 F) = 1` used by the published
`FiniteExtension.valuation_completionMap`. The main theorem
`isZero_H2_localUnits` proves `H²(Gal(E_w/F_v), U_w) = 0` under one more
hypothesis: `H²(Gal(E_w/F_v), E_wˣ)` is finite and has at most
`[E_w : F_v]` elements. Here `U_w` is the published
`localUnitsRepresentation v w` of valuation units. The second hypothesis is
part of local class field theory. In the intended use it comes from the
injectivity and image conditions of a local invariant family (the published
`InvariantFamily.RelativeImages`). This module does not prove it.

Only degree `2` is treated. No other degree, Tate cohomology or norm
surjectivity on units is proved.

## The decomposition group is cyclic

- `mem_range_decompositionHom_iff_mem_stabilizer` (for `E / F` normal): an
  element `g ∈ Gal(E/F)` lies in the image of the published
  `decompositionHom v w` exactly when it lies in Mathlib's stabilizer of the
  prime ideal `w.asIdeal` for the pointwise action on ideals of `𝓞 E`. The
  published `mem_range_decompositionHom_iff` describes the image by
  `finitePlaceEquiv g.toRingEquiv w = w`. That place has prime ideal
  `w.asIdeal.comap g`, and `x ∈ g • w.asIdeal` exactly when
  `g⁻¹ • x ∈ w.asIdeal`. The two conditions are related by passing from `g`
  to `g⁻¹`, and the image is a subgroup.
- `isCyclic_stabilizer`: if the ramification index is `1`, then the
  stabilizer of `w.asIdeal` in `Gal(E/F)` is cyclic. By Mathlib's
  `Ideal.card_inertia_eq_ramificationIdxIn` and
  `Ideal.ramificationIdxIn_eq_ramificationIdx`, the inertia group has one
  element. By `Ideal.Quotient.map_ker_stabilizer_subtype`, the kernel of
  Mathlib's `Ideal.Quotient.stabilizerHom` is trivial. So the stabilizer
  embeds into the Galois group of the residue field extension
  `(𝓞 E ⧸ w) / (𝓞 F ⧸ v)`, which is cyclic because these fields are finite.
- `isCyclic_localGal`: `Gal(E_w/F_v)` is then cyclic. The published
  `decompositionHom_injective` embeds it into the stabilizer.

## `H²` of the integers for a cyclic group

- `card_le_card_H2_trivial_integers`: let `G` be a finite cyclic group, and
  assume that `H²(G, ℤ)` (trivial action, scalars `ULift ℤ`) is finite. Then
  it has at least `|G|` elements. Mathlib's
  `Rep.FiniteCyclicGroup.groupCohomologyπEven` maps the kernel of `g - 1` to
  `H²(G, ℤ)` for a generator `g`. For trivial action this kernel is all of
  `ℤ`, and two integers have the same image exactly when their difference is
  a multiple of `|G|`, the image of the norm map
  (`groupCohomologyπEven_eq_iff`). So the classes of `0, 1, …, |G| - 1` are
  distinct.

## Splitting the valuation sequence

- `exists_fixed_uniformizer`: if the ramification index is `1`, there is a
  unit `π` of `E_w` whose valuation exponent (the published `unitsExponent`)
  is `-1` and which is fixed by every `σ ∈ Gal(E_w/F_v)`. Take the image of a
  uniformizer of `F_v`. By the published `valuation_completionMap`, its
  valuation in `E_w` is its `F_v`-valuation raised to the power `1`. It is
  fixed because each `σ` is `F_v`-linear.

For such a `π` (hypotheses `hπ1` for the exponent, `hπ` for the fixedness):

- `integersSection hπ : ℤ ⟶ E_wˣ` sends `m` to `π ^ (-m)`. It is a morphism
  from Mathlib's trivial representation because `π` is fixed.
- `unitsRetraction hπ1 hπ : E_wˣ ⟶ U_w` sends `x` to `x · π ^ (ord x)`,
  where `ord` is the valuation exponent. This unit has exponent `0`. The map
  is equivariant because `π` is fixed and, by the published
  `unitsExponent_localAut`, `ord` is invariant.
- `localUnitsInclusion_comp_unitsRetraction`: the published inclusion
  `U_w ⟶ E_wˣ` followed by the retraction is the identity.
  `integersSection_comp_unitsExponentMorphism`: the section followed by the
  published exponent morphism `E_wˣ ⟶ ℤ` is the identity.
  `integersSection_comp_unitsRetraction`: the section followed by the
  retraction is zero.

## The vanishing theorem

`isZero_H2_localUnits`: with the hypotheses at the top of this page,
`H²(Gal(E_w/F_v), U_w)` is zero. Write `i`, `r`, `s`, `o` for the maps on
`H²` induced by the inclusion, the retraction, the section and the exponent.
The identities above give `r ∘ i = id`, `o ∘ s = id` and `r ∘ s = 0`. The
published short complex `unitsValuationSequence` gives `o ∘ i = 0`. Hence
`(a, b) ↦ i a + s b` is injective from `H²(U_w) × H²(ℤ)` into
`H²(E_wˣ)`. So `H²(ℤ)` and `H²(U_w)` are finite, and
`|H²(U_w)| · |H²(ℤ)| ≤ |H²(E_wˣ)| ≤ [E_w : F_v]`. Here
`[E_w : F_v] = |Gal(E_w/F_v)|`, because `E_w / F_v` is Galois by the
published `isGalois_adicCompletion`, and `|Gal(E_w/F_v)| ≤ |H²(ℤ)|` by the
cyclic count. Therefore `|H²(U_w)| ≤ 1`.

The private helpers `H2map`, `H2map_comp_apply`, `H2map_id_apply` and
`H2map_zero_apply` express the degree-two maps as functions and record their
functoriality.

## Sources and provenance

Milne, *Class Field Theory* (v4.03, 2020), Chapter III §1, Proposition 1.1
and its proof, printed pp. 97–98 (PDF pp. 106–107), proves that
`Ĥʳ(G, U_L) = 0` for an unramified extension of local fields. A prime element
of `K` gives a decomposition `Lˣ ≅ U_L × ℤ` of `G`-modules, so `Hʳ(G, U_L)` is
a direct summand of `Hʳ(G, Lˣ)`. The text before Lemma 1.3 (printed p. 98,
PDF p. 107) notes that `G ≅ Gal(l/k)` for the residue fields. Milne then uses
`H¹(G, Lˣ) = 0`, periodicity for the cyclic group `G`, and the surjectivity
of the unit norm (Proposition 1.2).

This module uses the same splitting but a different final step. It counts
elements and uses the hypothesis `|H²(G, E_wˣ)| ≤ [E_w : F_v]`, so Milne's
Proposition 1.2 is not needed. The cyclicity proof through the global
stabilizer and Mathlib's inertia group, the count `|H²(G, ℤ)| ≥ |G|`, and the
form of the hypotheses are internal.
