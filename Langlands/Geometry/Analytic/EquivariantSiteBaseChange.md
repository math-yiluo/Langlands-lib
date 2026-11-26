# Base change of equivariant analytic site objects

For a fixed-field morphism `f : Y ⟶ X` of spaces with operators, its group
homomorphism `H → G` restricts the action on `X` to `H`. The map `restrictedHom f`
is the original analytic map equipped with its resulting `H`-equivariance.
`etalePullbackFunctor f` and `quasiEtalePullbackFunctor f` send an equivariant
site object `U → X` to the pullback `U ×_X Y → Y` with the diagonal `H`-action.
The functors first restrict the group along `H → G` and then use Mathlib's
morphism-property over-category pullback. Its map on arrows is induced by the
two projections of the pullback. The projection declarations and the last
two theorems identify the square in the localized category of analytic spaces.

In `GSpace`, pullbacks along a quasi-étale morphism use the actual localized
analytic pullback and `pullbackOfForget`, which makes it a Hausdorff space with
a continuous diagonal action and equivariant projections. The forgetful
functor reflects pullbacks because the forgetful functor on actions reflects
limits and `GSpace` is a full subcategory. Existence then gives preservation
of each such pullback. Base change preserves the quasi-étale property here by
`quasiEtale_of_isPullback_of_t2Space` since the source of a `G`-morphism is
Hausdorff. For étale maps the proof uses `localizedEtaleBaseChange` and the
inclusion of étale maps in the quasi-étale class. These facts supply the
instances for the over-category pullback functors.

The field is complete and ultrametric. The group universe is independent of
the field and space universes, and each space and its atlas index use the
same universe. The construction concerns the categories underlying the two
sites. Conditions on the induced functors for covering sieves are separate
from the categorical pullback calculation.

## Original sources

- V. G. Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*,
  unfinished manuscript (1995–1996), §1.2, printed/PDF p. 3, uses
  `(X′ ×_X U)(G′)` as the base change of an equivariant object `U(G)`.
  Literature ID `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
  folder SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
  member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
  member SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
- V. G. Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115
  (1994), Lemma 3.1(i), printed p. 544 (PDF p. 6), gives quasi-étale stability
  under base change. Literature ID `berkovich-1994-vanishing-cycles-formal-schemes`,
  SHA-256 `f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`.
- V. G. Berkovich, *Étale cohomology for non-Archimedean analytic spaces*,
  Publ. Math. IHÉS 78 (1993), Proposition 1.4.1, printed pp. 29–30 (PDF pp.
  26–27), constructs analytic fibre products. Literature ID
  `berkovich-1993-etale-cohomology`, SHA-256
  `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
