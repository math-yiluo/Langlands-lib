# Discreteness of rational and integral points in adelic points

Author: Worker 105.

`AdelicRationalPointsDiscreteStatement` states the adelic part of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.3, Examples 2.2 and 2.3. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Example 2.2 names the inclusions of `F` into `A_F` and of `O_{F,S}` into
`A_{F,S}`, "with the subring having the discrete topology in both cases".
It ends: "if R is discrete in R′ then X(R) is discrete in X(R′)". Example
2.3 says that for every affine finite type `F`-scheme `X`, the map
`X(F) → X(A_F)` "is a topological embedding onto a discrete subset". It adds
that for `X` affine of finite type over `O_{F,S}`, the set `X(O_{F,S})` is a
discrete subset of `X(A_{F,S})`. This statement does not include the third
sentence of Example 2.3, about discrete valuation rings. That sentence is
formalized separately in `DvrPointStatements`.

## The general transfer

`AffineDiscreteCoefficientConclusion R T` concerns a commutative ring `R`,
a commutative topological `R`-algebra `T`, and the discrete topology on `R`.
The discrete topology is put on `R` inside the proposition, so `R` needs no
topology of its own. The proposition quantifies over all `X` over `Spec R`
with `X.left` affine and the structure map locally of finite type. For
affine `X` this is exactly "affine of finite type", because an affine scheme
is quasi-compact. Point sets are the actual relative scheme morphisms from
`Spec R` or `Spec T` to `X` over `Spec R`. Both carry the published
global-section evaluation topology. `RingPoint.changeRing` along the
structure map `Algebra.ofId R T` is precomposition with the actual
spectrum map. The conclusion has two parts. This point map is a topological
embedding, and its image with the subspace topology is discrete. This is
the map `X(R) → X(T)`; Conrad writes its target as `X(R′) = X′(R′)`. The
comparison with points of the base change `X′` is a separate published
interface and is not used here.

`AffineDiscreteSubringProperty R T` states this conclusion under two
hypotheses: the structure map `R → T` is injective, and its image is
discrete in the subspace topology. Conrad's phrase "R is discrete in R′"
names a subring with these two properties. The conclusion includes the
embedding, as in Example 2.3. When `R` is discrete, injectivity and a
discrete image make `R → T` an embedding, and Example 2.2 transfers
embeddings to points. The first clause of `AdelicRationalPointsDiscreteStatement`
asserts this property for every such pair `R`, `T`. No topological ring
structure on `T` is assumed.

## The arithmetic clauses

`NumberFieldRationalPointsDiscreteStatement` asserts the conclusion for
every number field `K` and its full adele ring `Adeles K`, including the
archimedean factors, with Mathlib's diagonal algebra structure. This is the
first sentence of Example 2.3 in characteristic zero.

`NumberFieldIntegralPointsDiscreteStatement` asserts it for every finite set
`S` of finite places. The coefficient ring is Mathlib's ring of `S`-integers
`(S : Set (FinitePlace K)).integer K`. The value ring is the published
level `numberFieldAdeleLevel K S`, with its published diagonal algebra
structure. That level is the subring of `Adeles K` integral at every finite
place outside `S`, with all archimedean factors unrestricted, and it carries
the subspace topology. Conrad's `S` contains all archimedean places; here
`S` lists only the finite ones and the level adds every archimedean place.
The empty finite set, which gives the ring of integers, is included.

`CurvePlaceRationalPointsDiscreteStatement` asserts the conclusion for a
function field `F` over `k`. Here `F` is a finite extension of `RatFunc k`
with compatible actions of `k` and `RatFunc k`. The value ring is the
published `CurvePlaceAdeleRing k F`: the restricted product of the
completions at all places of `F` trivial on `k`. Its algebra structure is
the published full diagonal `curvePlaceAdeleDiagonal`. That diagonal is
constructed only for a perfect constant field, so this clause assumes
`PerfectField k`. Finite fields are perfect, so all global function fields
are covered.

`CurvePlaceIntegralPointsDiscreteStatement` asserts it for every finite set
`S` of these places. The coefficient ring is `curvePlaceSIntegers k F S`,
the elements of `F` integral at every place outside `S`. The value ring is
the level `curvePlaceAdeleLevel k F S`, integral outside `S`, with the
subspace topology and the published diagonal algebra structure
`curvePlaceAdeleLevelDiagonal`. This construction needs no full diagonal,
so here `k` is an arbitrary field with no perfectness assumption, and every
finite `S`, including the empty set, is allowed. Conrad's sets `S` are
nonempty for function fields. The clause therefore covers his cases and
more.

All five clauses are stated in one arbitrary universe and combined by
conjunction in `AdelicRationalPointsDiscreteStatement`.

## Provenance

The arithmetic clauses are the source's assertions for the published
carriers. The following parts are derived from the source rather than
quoted from it. The general clause makes Conrad's closing remark in
Example 2.2 precise and adds the embedding claim of Example 2.3. The
integral clauses add the embedding claim, which Conrad states only for
rational points. The function-field integral clause allows an arbitrary
constant field and every finite `S`. The rational function-field clause
assumes a perfect constant field, which is needed for the published
diagonal. No clause assumes any part of its conclusion.
