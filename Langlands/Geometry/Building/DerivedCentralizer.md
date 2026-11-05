# Actual centralizer transport and full V6 through a derived inclusion

The centralizer map is an internal construction over a field `F : Type u`.
Take commutative group schemes `T`, `A`, `S`, group schemes `D`, `G`, a square
`j ≫ d = e ≫ i`, splitness of `T` and `A`, and an actual flat-surjective product
of `e : T → S` and `c : A → S`. The composite `c ≫ i` is central on every test
scheme. This part requires neither derivedness of `d` nor monomorphic
embeddings, maximality, or an isogeny.

`derived_map_mem_torusCentralizer` proves that the original map of `d` sends
the all-test centralizer of `j` into that of `i`. For a source centralizer
point, its image commutes with the retained torus by the original square and
with the central complement by centrality. It therefore commutes with their
product. The existing faithfully flat change-of-acting-group lemma
`TorusCoverTransport.map_mem_torusCentralizer`, applied to the product and the
identity of `G`, descends this assertion to the full ambient torus. This
argument uses scheme flatness and surjectivity, not surjectivity on rational
points.

Let `CS : CentralizerDatum j` and `CT : CentralizerDatum i` be supplied actual
centralizer data, including their original closed representatives, acting
torus factors and bijective restriction-evaluation maps.
`range_derived_centralizer_comp_le` applies the all-test result to the source
representative. `derivedCentralizerMap` factors `CS.j ≫ d` uniquely through
the actual ambient centralizer representative. Its two proved identities are

```text
derivedCentralizerMap ≫ CT.j = CS.j ≫ d
CS.s ≫ derivedCentralizerMap = e ≫ CT.s.
```

The first is the defining factorization; the second follows by cancellation
through the actual represented ambient subgroup and the original torus square.

Over a nonarchimedean local field, `derivedCentralizerMap_translation` proves

```text
cocharacterMapReal e (CS.translation z)
  = CT.translation (derivedCentralizerMap(z)),
```

where the displayed vectors are the additive forms of the original
`ν = -ω_Z`. This is an equality of full real torus vectors. It follows from the
existing character-normalized translation naturality theorem applied to the
proved torus-centralizer square and the supplied restriction-evaluation
bijections.

For the full V6 transfer, add the actual derived inclusion condition,
affineness and local finite type of `D`, affineness and smoothness of `G`,
and splitness of `S`, as in `DerivedFunctions`.
`IsCentralizerCompatible.derivedPullback` proves the original full V6
predicate on `CS` for the literal derived pullback of every ambient family
satisfying full V6 on `CT`.

The proof chooses the corresponding ambient root. Source centralizer
conjugation preserves that source root subgroup. Evaluating the literal
pullback and the original point-map multiplication laws identifies this
conjugation with ambient centralizer conjugation through the constructed map.
The translation-vector identity and the character evaluation formula identify
the scalar terms in V6. Applying the original ambient V6 equation finishes
the proof.

With both torus embeddings monomorphic and `i` an actual maximal split torus,
`KPApartmentData.IsOmegaCompatible.derivedPullback` transfers full V6 to the
entire actual derived apartment constructed in `DerivedApartment`. Every
point in its carrier has an ambient preimage, so the family result applies
pointwise.

This internal argument adapts `CentralIsogenyCentralizer` using the actual
derived root bijection and a retained/central product instead of an isogeny
of the full acting tori. No new external theorem is asserted.
Both actual centralizer data and all structural tori remain supplied. This
module does not prove their existence, source apartment axioms, unconditional
opposite-pair existence, or the final simply connected normalizer image
equality.
