# Analytifications of algebraic spaces, tested on affine points

This module defines when an analytic space `Y` with a family of maps `p` is an
analytification of an algebraic space `X` over `Spec K`. Here `Y` is an object of
the Library's localized category of analytic spaces. The family `p` assigns a
morphism `Spec(A)ᵃⁿ → Y` to every `A`-valued point of `X` and every finite
polynomial presentation of `A`. The predicate `IsAnalytification` asks that these
maps be natural in the test algebra, étale for étale points and jointly
surjective from étale points. It also asks that they carry fibre squares of
affine test points to pullback squares. The module also defines the analytic point
attached to a `K`-point and proves that composing with an isomorphism `Y ≅ Y'`
preserves the predicate.

The module makes no existence, uniqueness or comparison claim. In particular it
does not state that an analytification exists for a separated algebraic space,
that it is unique up to unique isomorphism, or that its rational points are the
`K`-points of `X`. Those are stated in other modules, among them
`SpaceAnalytificationExistenceStatement` and
`SpaceAnalytificationRationalPointsStatement`.

## Provenance

The sources are Conrad–Temkin, *Non-archimedean analytification of algebraic
spaces* (2009), registered as
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`. The second
source is Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Conrad, printed p.19, in the proof of Proposition 5.11(3), uses the main theorem
of Conrad–Temkin. It gives a functorial analytification `Xᵃⁿ` for separated
algebraic spaces `X` locally of finite type over `k`. This analytification is
compatible with fibre products, open and closed immersions, étale maps, the
scheme case and extension of the ground field. By [CT, Ex. 2.3.2] it satisfies
`X(k) = Xᵃⁿ(k)` as sets.

Conrad–Temkin, §2.2, printed pp.7–8, work with rigid-analytic spaces and fix an
étale chart `R ⇉ U` of `X`.
Definition 2.2.2 calls `X` analytifiable when the quotient sheaf `Uᵃⁿ/Rᵃⁿ` is
representable, and defines `Xᵃⁿ` as this quotient. Lemma 2.2.1 shows that the
quotient does not depend on the chart. Theorem 2.2.3 makes `X ↦ Xᵃⁿ` a functor
compatible with fibre products and with open and closed immersions. Theorem
2.3.1, printed p.11, says that `f` is étale if and only if `fᵃⁿ` is. In the
`k`-analytic setting, Definition 4.1.1, printed p.18, defines a quotient of an
étale equivalence relation `R ⇉ U` as an analytic space `X` with an étale
surjection `U → X`. The two composites `R ⇉ U → X` must coincide and
`R → U ×_X U` must be an isomorphism. The paragraph after Example 4.1.3,
printed p.19, explains that such a quotient represents the quotient sheaf
`U/R` on the étale site, so it is unique up to unique isomorphism. The end of
the proof of Lemma 4.2.3, printed p.21, uses the same criterion. Theorem 4.2.1
and Theorem 4.2.2, printed p.20, prove that the quotient exists for a separated
algebraic space. The proof analytifies an étale chart to good strictly
`k`-analytic spaces `R ⇉ U` with `R → U × U` a closed immersion.

## Derived formulation

The Library has no category of étale sheaves on its analytic spaces and no
quotient sheaves. This module therefore uses the representability criterion of
Definition 4.1.1 directly, not the quotient sheaf. It does not fix one chart.
Instead it asks for compatible maps from the analytifications of all affine test
points, which builds in the chart independence of Lemma 2.2.1. The derivation
is as follows.

Let `X` be separated and locally of finite type, and choose étale points
`xᵢ : Spec Aᵢ → X` whose images cover `X`. Then each
`Spec Aᵢ ×_X Spec Aⱼ` is a closed subscheme of `Spec Aᵢ ×_K Spec Aⱼ`, so it is
an affine scheme `Spec Cᵢⱼ`. The fields of `IsAnalytification` give the
following.
- The maps `p(xᵢ) : Spec(Aᵢ)ᵃⁿ → Y` are étale (`etale_map`) and jointly
  surjective (`jointly_surjective`).
- The two composites `Spec(Cᵢⱼ)ᵃⁿ ⇉ Spec(Aᵢ)ᵃⁿ, Spec(Aⱼ)ᵃⁿ → Y` agree, because
  both equal the map attached to the common restriction of `xᵢ` and `xⱼ`
  (`naturality`).
- `Spec(Cᵢⱼ)ᵃⁿ` is the fibre product `Spec(Aᵢ)ᵃⁿ ×_Y Spec(Aⱼ)ᵃⁿ`
  (`isPullback`).

Chartwise, these are the conditions of Definition 4.1.1 for the analytified
chart. In the other direction, Conrad–Temkin's `Xᵃⁿ` has all four properties:
naturality from Theorem 2.2.3, the étale condition from Theorem 2.3.1, joint
surjectivity because `Uᵃⁿ → Xᵃⁿ` is surjective, and the pullback condition from
compatibility with fibre products (Theorem 2.2.3) together with the affine
scheme case. These comparisons are motivation only. Neither direction is stated
or proved in this module for the Library's model.

The predicate is defined for every algebraic space over `Spec K`. It is intended
as Conrad–Temkin's notion only for separated `X` locally of finite type over `K`,
the case that Conrad's paper uses. For other `X`, the fibre-square condition
only sees fibre products that happen to be affine, and no claim is made that the
predicate characterizes Conrad–Temkin's `Xᵃⁿ`. Conrad–Temkin's rigid-analytic
statement assumes a nontrivial absolute value, and here `K` is a nontrivially
normed field. The analytic spaces are objects of the Library's localized
category `SaturatedAtlasPresentation.LocalizedCategory`, not Berkovich's
category itself.

## Hypotheses

Everything lies in `Langlands.Analytic.SpaceAnalytification`. The field `K` in
universe `u` is nontrivially normed, ultrametric and complete. `X` is an
algebraic space over `Spec K`, in the Library's sense
(`Langlands.AlgebraicGeometry.AlgebraicSpace`). `Y` is an object of
`LocalizedCategory.{u, u, u}` over `K`. Test algebras `A` are commutative
`K`-algebras in universe `u`.

## Declarations

`pointHom K x` is the morphism of presheaves `Spec A → X` attached to a point
`x : RingPoints K X A` by the inverse of the Yoneda equivalence
`uliftYonedaEquiv`. Its source is `schemeYoneda (Spec K)` applied to the
Library's `ringTest K A`, the spectrum of `A` over `Spec K`.

`PointFamily K X Y` is the type of families `p` that assign to each
commutative `K`-algebra `A` in universe `u`, each finite polynomial
presentation `P : FinitePolynomialPresentation K A` and each point
`x : RingPoints K X A` a morphism `AffineAnalytification.localized K P ⟶ Y`.
The source is the Library's analytification of `Spec A` built from `P`.

`IsAnalytification K X Y p` is a structure in `Prop` with four fields.
1. `naturality`: for presentations `P` of `A` and `Q` of `B`, a `K`-algebra map
   `f : A →ₐ[K] B` and a point `x` of `X` over `A`,
   `p B Q (RingPoints.changeRing f x)` equals
   `AffineAnalytification.localizedHom K P Q f ≫ p A P x`. Here
   `RingPoints.changeRing f x` is the restriction of `x` along
   `Spec B → Spec A`, and `localizedHom K P Q f` is the published analytified
   map `Spec(B)ᵃⁿ → Spec(A)ᵃⁿ`. Taking `f` to be the identity with two
   presentations shows that the maps for different presentations of the same
   algebra correspond under the change-of-presentation map.
2. `etale_map`: if `pointHom K x` is étale in the Library's sense
   `AlgebraicSpace.IsEtale`, so that every represented base change along a
   scheme point is an étale scheme morphism, then `p A P x` lies in the Library's
   class `SaturatedAtlasPresentation.etale` of étale morphisms of the localized
   category.
3. `jointly_surjective`: every point `y` of the underlying topological space
   `localizedSpaceFunctor.obj Y` lies in the image of
   `localizedSpaceFunctor.map (p A P x)` for some `A`, some presentation `P` and
   some point `x` with `pointHom K x` étale.
4. `isPullback`: let `P`, `Q`, `R` present `A`, `B`, `C`, and let
   `f : A →ₐ[K] C` and `g : B →ₐ[K] C` be algebra maps, `x` an `A`-point and
   `y` a `B`-point of `X`. Suppose the square of presheaves formed by
   `Spec C → Spec A`, `Spec C → Spec B` (the images of `ringTestMap K f` and
   `ringTestMap K g` under `schemeYoneda`), `pointHom K x` and `pointHom K y` is a
   pullback. Then the square in the localized category formed by
   `localizedHom K P R f`, `localizedHom K Q R g`, `p A P x` and `p B Q y` is a
   pullback.

The hypothesis of field 4 says that `Spec C` is the fibre product
`Spec A ×_X Spec B` with its two projections. It implies that the two points
restrict to the same `C`-point, but field 4 does not assume this separately.

`rationalPoint p P₀ x` is the analytic point attached to a `K`-point
`x : RingPoints K X K`. For a presentation `P₀` of `K`, it is the image under
`localizedSpaceFunctor.map (p K P₀ x)` of the published
`AffineAnalytification.analyticPoint K P₀` of the identity `K`-point of `K`.
It is the map `X(K) → Xᵃⁿ` of [CT, Ex. 2.3.2]; no injectivity or bijectivity is
claimed here.

## Lemmas

`IsAnalytification.comp_iso hp e` shows that if `(Y, p)` satisfies the
predicate and `e : Y ≅ Y'`, then `(Y', p · ≫ e.hom)` satisfies it too. The
proof is as follows.
- Naturality follows by associativity.
- The étale condition holds because the Library's class `etale` respects
  isomorphisms (`MorphismProperty.RespectsIso.postcomp`).
- For joint surjectivity, a point `y` of `Y'` is first moved to `Y` by
  `e.inv`. Then `localizedSpaceFunctor` turns `e.inv ≫ e.hom = 𝟙` into the
  identity map.
- Pullback squares are transported along `e` by `IsPullback.of_iso`.

`rationalPoint_comp_iso` says that the rational point attached to the composed
family is the image under `localizedSpaceFunctor.map e.hom` of the original
rational point. Its proof unfolds `rationalPoint` and uses functoriality of
`localizedSpaceFunctor`.
