# Quotient morphisms into a greatest-chart target

This module constructs an equivalence between global complete strong maps and actual source-subatlas quotient morphisms when the target has a greatest original chart. It is an internal consequence of the previously constructed strong extension from refining source selections and complete bounded-map faithfulness of the original strong-map functor. It makes no new assertion of original-literature correspondence.

The coefficient field `K : Type u` is complete and has ultrametric distance. The objects `A`, `B` and `C` are actual `SaturatedAtlasPresentation.{u,v,w} K`, with independent field, ambient-space and chart-index universes. The target comes with an original index `t` and a proof that the image of every original target chart lies in the image of chart `t`. The source quotient is the existing quotient of actual complete strong numerators on downward closed locally refining selections of the original source charts. Its common-source equivalence relation and category structure are unchanged. No global representative, point-map faithfulness, reducedness, nontrivial valuation or nonempty spectrum is an input.

## Constructing the Hom equivalence

`strongFunctor_map_extendTop` proves that extending any complete numerator `g` from a refining original source selection gives its original quotient class. The formula `strongFunctor_map_eq_ι` computes the global map's class on that particular selection. Categorical precomposition by the actual inclusion equals literal strong source restriction. The preceding extension's full restriction recovery theorem then identifies its numerator with `g`, including every admissible bounded algebra pullback.

`strongFunctor_map_surjective_of_top` uses quotient induction. Each representative consists of a selection and an actual complete numerator. Its strong extension is a global map with the required quotient class, by the preceding formula. The independent full bounded-map source separation result already proves injectivity of `strongFunctor.map`; equality of spectrum point functions is not used to deduce equality of algebra maps.

`topTargetHomEquiv` applies `Equiv.ofBijective` to this proved bijection. Its forward map is the original strong-map functor. `strongFunctor_map_topTargetHomEquiv_symm` proves that inverse recovery represents exactly the given quotient arrow, and `topTargetHomEquiv_symm_ι` identifies the inverse on every actual numerator with the constructed `extendTop`. Thus the inverse recovers the whole global strong map, beyond its continuous point function. `topTargetHomEquiv_eq` proves independence of the greatest-chart choice by extensionality of the fixed forward maps.

## Continuous maps and naturality

`topTargetHomEquiv_symm_spaceMap` identifies the recovered global continuous map with the existing space functor on the input quotient arrow. Apply that functor to the inverse recovery equation and use its original strong-map formula.

`topTargetHomEquiv_symm_precomp` commutes inverse recovery with precomposition by an arbitrary global complete strong map. Only the final target needs a greatest chart; the new source does not. `topTargetHomEquiv_symm_postcomp` commutes recovery with postcomposition by a global complete strong map when both targets have greatest charts. `topTargetHomEquiv_symm_comp` computes global strong composition for arbitrary quotient arrows whose intermediate and final targets have greatest charts. Each proof applies the already proved faithful strong-map functor, its composition law and the inverse recovery equations.

This focused result concerns the existing saturated source-quotient category and greatest-chart targets. The actual fully faithful affinoid embedding, identification with the full analytic category, etale and equivariant sites, and Harris tower specialization remain separate construction obligations.
