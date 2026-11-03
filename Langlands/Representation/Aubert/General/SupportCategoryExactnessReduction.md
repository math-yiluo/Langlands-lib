# Exactness detection from zero detection

Implementation and documentation: Worker 499. Worker 379's published support
category, support targets and subquotient-closure proof are reused with retained
authorship.

This is an internal construction and reduction, derived from the actual smooth
representation category and the published normalized Jacquet exactness theorem.
It supplies the actual image projection and quotient descent, their
factorization laws, and the elementary functor arguments that reduce exactness
detection to zero detection. The main reduction has an explicit zero-detection
premise. It does not prove the rational zero-detection or rational exactness
target.

All declarations below are in
`Langlands.Aubert.General.ExactnessDetection`. The only direct import is
`Langlands.Representation.Aubert.General.SupportCategoryStatements`.
Every object and morphism is an actual smooth complex representation or
equivariant linear map.

## Actual constructions

For any topological group `G`, objects `A,B : SmoothRep ℂ G` and morphism
`f : A ⟶ B`, `imageProjection f : A ⟶ SmoothRep.image f` is the actual
linear map with range restricted to the invariant image of `f`. Its
equivariance follows from that of `f`, using subtype extensionality.
`imageProjection_surjective` chooses the preimage from membership in the
linear range. `imageProjection_imageι` states
`imageProjection f ≫ SmoothRep.imageι f = f`; it is definitional.

For `f : A ⟶ B`, `g : B ⟶ C` and `hfg : f ≫ g = 0`,
`cokernelDesc f g hfg : SmoothRep.cokernel f ⟶ C` descends `g` through the
actual quotient of `B` by the invariant range of `f`. The underlying linear
map is `Submodule.liftQ`. The complex condition makes `g` vanish on that range,
and equivariance is checked on quotient representatives.
`cokernelπ_cokernelDesc` states
`SmoothRep.cokernelπ f ≫ cokernelDesc f g hfg = g`; it too is definitional.

These constructions and their laws have no local compactness,
nonarchimedean, length, admissibility or support hypothesis. The group and
representation-carrier universes are independent.

## Preservation of arbitrary exact pairs

`MapsShortExact F : Prop` means that a functor
`F : SmoothRep ℂ G ⥤ SmoothRep ℂ H` preserves every actual short exact
sequence. The source and target group universes are independent, and the
representation carriers have one common universe. Short exactness is the
Library's `SmoothRep.IsShortExact`: the first map is injective, the second
surjective, and their linear range and kernel are equal. There is no length
restriction.

`map_injective F hF f hf` applies `hF` to `f` followed by its actual
cokernel projection, so an injective map remains injective.
`map_surjective F hF f hf` applies `hF` to the actual kernel inclusion
followed by `f`, so a surjective map remains surjective.
`map_comp_apply` expresses functoriality on vectors:
`F(f ≫ g)(x) = F(g)(F(f)(x))`.

`map_exact F hF f g hex` proves preservation of
`Function.Exact (SmoothRep.hom f) (SmoothRep.hom g)`, where `f` and `g`
need not be injective or surjective. The proof factors both maps through
their actual images. Exactness gives the short exact sequence

`image(f) ↪ B ↠ image(g)`.

Apply `hF` to this sequence. The mapped projection from `A` onto `image(f)`
is surjective and the mapped inclusion of `image(g)` into `C` is
injective by the preceding lemmas. These facts transfer exactness of the
mapped middle sequence to the original pair. This argument uses no support
condition and imposes no conditions on the endpoint objects.

## Jacquet zero maps

`jacquet_map_zero h hU A B` proves that the actual normalized functor
`jacquetFunctor h hU` sends a zero morphism to zero. Here `G` is locally
compact and nonarchimedean, `h` is an actual semidirect decomposition
`P = M ⋉ U`, and `U` is closed.

Every vector in the normalized Jacquet module has a coinvariant
representative, by `Jacquet.Localization.mk_surjective`. On a representative,
the mapped zero morphism is the quotient image of zero, which is zero by
linearity. This lemma requires no compact-limit assumption.

## Reflection lemmas

Fix the generic standard-family data `P,M,U,h,hU,hM,hL,IsAssociate` of
`SupportCategoryStatements`, at independent universes `uI,uG,uV`. The
representation carriers have universe `max uG uV`. In this section:

- `hUc J` says that `U J` is a limit of compact subgroups.
- `hdet` is
  `SupportCategoryZeroDetectionTarget P M U h hU hM hL IsAssociate`.

Both are explicit hypotheses. Each detecting index includes both
`IsAssociate I J n` and the displayed equality of the conjugated Levi
subgroups, as required by the existing support targets.

`injective_of_jacquet hUc hdet f hA hf` reflects injectivity of `f : A ⟶ B`
when `A` belongs to the support category for `I` and every detecting Jacquet
map of `f` is injective. The actual kernel is a subrepresentation of `A`,
so it belongs to the same support category. Its inclusion stays injective
under each Jacquet functor by
`Langlands.Aubert.General.jacquetFunctor_map_isShortExact`.
The kernel inclusion composed with `f` is zero. Functoriality,
`jacquet_map_zero` and the hypothesized injectivity of the mapped `f` imply
that every Jacquet module of the kernel is zero. Apply `hdet` to the
kernel, and then the linear kernel criterion for injectivity.

`eq_zero_of_jacquet hUc hdet f hA hf` proves that a map `f : A ⟶ B`
from a support object is zero when every detecting Jacquet map is
pointwise zero. Its actual image is a quotient of `A`, hence in the same
support category. Map the factorization
`A ↠ image(f) ↪ B`. The first map remains surjective and the second
injective. Since their composite is zero, the mapped image is zero.
Apply `hdet` to the image, and use the actual image projection to conclude
that `f` vanishes.

Neither reflection lemma assumes that the target object belongs to a
support category.

## Full conditional exactness reduction

`supportCategoryExactnessDetection_of_zeroDetection hUc hdet` proves

`SupportCategoryExactnessDetectionTarget P M U h hU hM hL IsAssociate`.

For arbitrary `f : A ⟶ B` and `g : B ⟶ C` with `B` in the support
category for `I`, it proves the stated equivalence between exactness of
the underlying maps and exactness of their images under all associated
normalized Jacquet functors. There is no assumed complex condition.

The forward direction uses `map_exact` and full Jacquet short exactness.
For the converse the implemented proof is as follows.

1. The actual image of `f` belongs to the support category, since it is a
   subrepresentation of `B`. Set `s := imageι f ≫ g`. The mapped image
   projection is surjective. For a vector in its target, choose a
   preimage and apply the hypothesized exactness of the mapped `f,g`;
   this shows that every detecting Jacquet map of `s` is zero.
   `eq_zero_of_jacquet` gives `s = 0`. The factorization of `f` now
   gives `f ≫ g = 0`.
2. Form the actual quotient `Q := cokernel f`, the surjection
   `q : B ⟶ Q`, and the actual descended map `t : Q ⟶ C`.
   The quotient `Q` belongs to the support category. The pair `f,q`
   is exact by `Submodule.ker_mkQ`, so its image under every Jacquet
   functor is exact by `map_exact`; the mapped `q` is surjective.
3. To prove a mapped `t` injective, lift a vector in its kernel along
   the mapped `q`. The factorization `q ≫ t = g` puts that lift in
   the kernel of the mapped `g`. The assumed exactness of mapped
   `f,g` puts it in the image of mapped `f`. The exactness of mapped
   `f,q` then makes the original vector zero.
4. Apply `injective_of_jacquet` to `t` and the supported quotient `Q`.
   For any `v ∈ ker(g)`, injectivity of `t` gives `q(v) = 0`.
   The quotient kernel computation puts `v` in `range(f)`. The
   reverse inclusion follows from the derived complex condition.

Only `B` needs support. All smooth modules are allowed; finite length,
finite generation and admissibility are absent. Empty index sets and
rank-zero families are not excluded. Compact-limit and zero detection
remain hypotheses of this generic reduction and must be discharged in
any proof of the rational exactness target.

## Declaration dependencies and provenance

The representation-theoretic input used by this construction and its
laws is precisely the full Jacquet short-exactness theorem
`Langlands.Aubert.General.jacquetFunctor_map_isShortExact` from
`AlternatingOperator`, under `hUc`. Its proof uses
`Langlands.Jacquet.Localization.characterLocalizationExactness`, for
the trivial character and the actual normalizer action. Normalization
does not change the underlying maps. This input covers arbitrary
smooth objects, with no length bound.

Support closure is
`Langlands.Aubert.General.IsInSupportCategory.of_isSubquotient`
from `SupportCategory`; it uses the generic actual
`Langlands.smoothSubquotientTransitivity` theorem.
The actual subobject and quotient witnesses use
`SmoothRep.subrepresentation_isSubrepresentation`,
`SmoothRep.quotient_isQuotient`,
`SmoothRep.IsSubrepresentation.isSubquotient`, and
`SmoothRep.IsQuotient.isSubquotient`.
The last two elementary algebraic lemmas are housed in
`Classification.SupercuspidalSupport`; their proofs provide explicit
subobject–quotient witnesses and use no classification assertion.
Kernel, image, quotient and their maps are those of
`Category.Subquotients`. Other algebraic steps use
`LinearMap.exact_iff`, `LinearMap.ker_eq_bot`,
`Submodule.ker_mkQ`, `Submodule.range_subtype` and
`Submodule.Quotient.mk_eq_zero`.

The new reduction does not invoke a Langlands classification,
character-independence, geometric-lemma or adjointness theorem.
The separate premise `hdet` is not proved or expanded here; any later
specialization using a proof of zero detection must record that proof's
actual dependencies. No representation-theoretic consequence follows
merely from importing a module that contains targets for such results.

This internal argument is derived from the cited Library constructions
and linear algebra. It does not claim to formalize a new assertion from
the original literature or use Aubert's defective Proposition 3.2
application as proof evidence.
