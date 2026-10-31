# Radius-one comparison of relative finite etale actions

Authors: Worker 56 and Worker 36. The new comparison uses their strict
and generalized relative categories and the radius-one action comparison.

This internal derived construction transports the actual finite-etale
structural maps and all bounded equivariant triangles through the existing
radius-one quotient equivalences. It constructs a fully faithful relative
embedding and the natural continuous-spectrum comparison over the
identified base. The field and group occupy independent universes.
No coefficient completeness or nontrivial valuation is required.

The algebraic finite-etale condition is the conjunction of finiteness
and etaleness of the actual ring map. Both directions of the quotient
equivalence are bijective bounded algebra maps, hence algebraically finite
etale. Composition proves preservation in
`algebraicallyFiniteEtale_ofStrictMap`. Conjugation back and the explicit
inverse identities prove reflection in
`algebraicallyFiniteEtale_ofStrictMap_iff`. These assertions concern the
algebraic condition, without asserting analytic etaleness over every domain.

The relative embedding `AlgebraicallyFiniteEtaleActionUnder.ofStrictFunctor`
applies the existing fully faithful action functor
to the actual undercategory, then lifts to the full finite-etale
subcategory using preservation of the structural property. The inverse
on relative arrows uses Mathlib's fully faithful undercategory
construction, reflecting the commuting triangle. Its underlying bounded
map is the existing explicit `fromStrictMap`. The two bounded-map inverse
identities prove full faithfulness of this relative embedding in
`strictRelativeFullyFaithful`, supplying the `Full` and `Faithful` instances.
Forgetting the structural map commutes definitionally with it in
`ofStrictFunctor_forget`.

Within the namespace `AlgebraicallyFiniteEtaleActionUnder`, the concrete
map declarations have the following meanings.

| Declaration | Actual bounded-map formula |
| --- | --- |
| `ofStrictFunctor_obj_baseMap` | The image structural map is `ofStrictMap K Y.baseMap`. |
| `ofStrictFunctor_map_homMap` | The image of every relative arrow is `ofStrictMap` of its original bounded map. |
| `fromStrictRelativeMap` | The fully faithful action comparison reflects the triangle through `Under.post` at the specified base `X`. |
| `homMap_fromStrictRelativeMap` | The inverse arrow has underlying bounded map `fromStrictMap K (homMap h)`. |

For topological groups `strictRelativeSpectrumComparison` uses the previously
constructed equivariant spectrum homeomorphisms to compare spectra over the
base. Its source is the strict relative spectrum functor followed by
`Over.map (strictActionSpectrumIso K G X).hom`; its target first takes the
opposite of the relative embedding and then the generalized relative spectrum
functor. Both functors land over the spectrum of the embedded base action. The base change is
postcomposition with the forward spectrum comparison, using `Over.map`.
`Over.isoMk` constructs each component from the target spectrum
isomorphism; pointwise naturality at the structural map proves its
triangle. The same naturality at every relative arrow proves naturality.
The formulas
`strictRelativeSpectrumComparison_hom_apply` and
`strictRelativeSpectrumComparison_inv_apply` state that the forward point
map evaluates `a` as `x (strictEquiv K Y.obj.right.obj.V a)` and the inverse
evaluates `a` as `x ((strictEquiv K Y.obj.right.obj.V).symm a)`. Joint continuity is inherited
from the concrete spectrum-action functors, with the published local
identity forgetful instance on `TopCat`.

This construction claims neither essential surjectivity on arbitrary
positive-polyradius objects nor identification with Berkovich's analytic
automorphism topology. It constructs no atlas, analytic covering or site.
It allows zero quotients and empty spectra.

The geometric motivation is Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), Definition 3.3.1(i), printed/PDF page 17,
and Definition 3.3.9(i), printed/PDF page 19. These concern finite Banach
algebras and finite etaleness over every affinoid domain. The exact
comparison here is internally derived from the existing quotient
equivalences, full bounded-map relative categories and spectrum functors.
The source's complete-field analytic setting is not asserted for the
incomplete-field normed quotient scope allowed here.

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*
(unfinished manuscript, 1996), sections 1.1-1.2, printed/PDF pages 1-3,
motivates continuous actions and relative equivariant categories. Its
varying-field analytic actions and analytic automorphism topology are
distinct from this internal fixed-field norm-orbit prerequisite.

Registered originals: `berkovich-2009-trieste-analytic-spaces`,
PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`;
and folder
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder digest
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The cited original pages were read directly and both PDF hashes verified.
