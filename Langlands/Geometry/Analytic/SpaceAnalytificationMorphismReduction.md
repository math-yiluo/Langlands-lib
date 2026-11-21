# Morphisms of analytifications from étale descent of morphisms

Author: Worker 910. This module uses the following:

- Worker 790's `hom_ext_of_etale_local_eq` (`EtaleHomGluing`).
- Worker 784's published `exists_point_of_isPullback`
  (`LocalizedPullbackPoints`).
- The published étale base change theorem
  `SaturatedAtlasPresentation.localizedEtalePullbackBaseChange`
  (`LocalizedEtalePullbackProof`), which proves
  `LocalizedEtalePullbackStatement.{u, v} K`.
- The compatibility lemma `IsAnalytification.comp_map_eq_of_comp_eq`
  (`SpaceAnalytificationMorphismCompatibility`).

This module defines one Prop-valued condition,
`SpaceAnalytificationMorphismEtaleDescentInput`. It then proves that this
condition implies the published proposition
`SpaceAnalytificationMorphismStatement.{u}`. The condition itself is not
proved here, and the module imports no unpublished statement. It is the
only premise: étale base change, an input of an earlier version of this
reduction, is now discharged by the published theorem
`localizedEtalePullbackBaseChange`.

## The definition

`SpaceAnalytificationMorphismEtaleDescentInput.{u}` is étale descent of
morphisms. It says: for every complete, ultrametric, nontrivially normed
field `K : Type u` and any objects `S` and `T` of
`LocalizedCategory.{u, u, u}`, the presheaf `U ↦ Hom(U, T)` on the small
étale site of `S` is a sheaf for the published topology `etaleTopology S`.
In Lean this reads
`Presieve.IsSheaf (etaleTopology S)
((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj T)`.
Below this condition is called H1.

The Library has no statement or proof of H1 yet. The same Hom-sheaf
property appears as an explicit hypothesis in several published modules,
among them Worker 790's `EtaleHomGluing`. Those hypotheses allow any
complete ultrametric normed field; H1 is specialized to nontrivially normed
fields and to the space universe `u`, which is all that the target needs.

## Lemmas

Throughout, `(Y', p')` and `(Y, p)` are analytifications of `X'` and `X`
in the sense of the published `IsAnalytification`. A *test point* is an
`A`-point `x` of an algebraic space, where `A` has a finite polynomial
presentation `P`. Its analytic map is `p A P x : (Spec A)^an ⟶ Y`. The
test point is *étale* when `AlgebraicSpace.IsEtale (pointHom K x)` holds.

### `IsAnalytification.hom_ext_of_etale`

This lemma uses H1 for the target `T`. Two morphisms `F G : Y' ⟶ T` are
equal if `p' x ≫ F = p' x ≫ G` for every étale test point `x` of `X'`.

The proof applies `hom_ext_of_etale_local_eq`. At each point of `Y'`, the
axiom `jointly_surjective` gives an étale test point whose image contains
that point. The axiom `etale_map` makes the analytic map of that test
point étale.

### `IsAnalytification.exists_hom_etale_compatible`

This lemma uses H1 for the target `Y` and needs `X'` separated. It
constructs `F : Y' ⟶ Y` with `p' x ≫ F = p (f x)` for every étale test
point `x` of `X'`.

The proof works on the small étale site of `Y'`, over the object `𝟙 Y'`.
It forms the sieve of étale objects `U ⟶ Y'` that factor as `g ≫ p' x`
for some test point `x`. Here `x` need not be étale.

1. The sieve is downward closed by precomposition.
2. The sieve is covering by `mem_etaleTopology_of_jointlySurjective`.
   Every point of `Y'` lies in the image of the étale analytic map of some
   étale test point.
3. On each arrow of the sieve, the value is `g ≫ p (f x)` for a chosen
   factorization. By `comp_map_eq_of_comp_eq`, this value does not depend
   on the factorization, and the chosen values form a compatible family.
4. H1 amalgamates the family into `F`.
5. For an étale test point `x`, the arrow `p' x` lies in the sieve, with
   factorization `g = 𝟙`. Then `valid_glue` gives `p' x ≫ F = p (f x)`.

### `IsAnalytification.exists_etale_chart_factorization`

This lemma is unconditional. Fix `a : S ⟶ Y` and a point `s` of `S`. The lemma
finds three things:

- an étale `e : U ⟶ S` whose image contains `s`;
- an étale test point `y` of `X`;
- a morphism `l : U ⟶ (Spec B)^an` with `l ≫ p y = e ≫ a`.

The proof runs as follows.

1. `jointly_surjective` gives an étale test point `y` and a point `α`
   with `p y (α) = a (s)`.
2. The published `localizedEtalePullbackBaseChange`, applied to the
   étale map `p y` and to `a`, gives a pullback `U` with legs `l` and `e`,
   where `e` is étale.
3. Worker 784's `exists_point_of_isPullback` lifts the matching pair
   `(α, s)` to a point of `U`. Hence `s` lies in the image of `e`. That
   theorem holds for every pullback square in `LocalizedCategory.{u, u, u}`.
4. The equation `l ≫ p y = e ≫ a` is the commutativity of the pullback
   square.

### `IsAnalytification.comp_eq_of_etale_comp_eq`

This lemma uses H1 and needs `X'` separated. Suppose
`F : Y' ⟶ Y` satisfies `p' y ≫ F = p (f y)` for every étale test point
`y`. Then `p' x ≫ F = p (f x)` holds for every test point `x`.

1. Two morphisms `(Spec A)^an ⟶ Y` are compared by
   `hom_ext_of_etale_local_eq`. This uses H1 with source `(Spec A)^an` and
   target `Y`.
2. At a point `s`, apply the previous lemma to `a = p' x`. This gives
   `e`, `l` and an étale test point `y` with `l ≫ p' y = e ≫ p' x`.
3. Then `e ≫ p' x ≫ F = l ≫ p' y ≫ F`, and this equals `l ≫ p (f y)` by
   the hypothesis on `F`.
4. `comp_map_eq_of_comp_eq`, applied to `l` and `e`, gives
   `l ≫ p (f y) = e ≫ p (f x)`.

## Main theorem

`spaceAnalytificationMorphismStatement_of_etaleDescent (h :
SpaceAnalytificationMorphismEtaleDescentInput.{u}) :
SpaceAnalytificationMorphismStatement.{u}`.

- **Existence.** `exists_hom_etale_compatible` produces `F`, compatible
  with étale test points. `comp_eq_of_etale_comp_eq` extends the
  compatibility to all test points.
- **Uniqueness.** Let `G` be compatible with all test points. Then `G`
  and `F` agree after composition with every étale `p' x`. So
  `hom_ext_of_etale` gives `G = F`.

The target's hypothesis `LocallyOfFiniteTypeOverBase X'` is not used.
Separatedness of `X'` is used.

## Provenance: internal

This is a proof reduction, not a transcription of a source theorem. The
proof builds the morphism étale-locally on charts and glues, which is the
usual strategy. No source is cited for these Lean statements.

`SpaceAnalytificationMorphismEtaleDescentInput` is the one input of that
gluing that the Library does not yet prove: descent of morphisms for the
étale topology of Berkovich 1993, §4.1 (H1). Étale base change, the other
geometric input, is the published theorem `localizedEtalePullbackBaseChange`.

In the literature, Berkovich 1993, Proposition 4.1.3 (printed p. 83),
proves that a presheaf represented by a `k`-analytic space good over the
base is a sheaf for the étale topology. Its proof of uniqueness does not
use goodness. Remark 4.1.5 (printed p. 84) says the proposition should
hold without goodness, and names the missing input: images of affinoid
domains under finite étale maps of affinoid spaces are finite unions of
affinoid domains. H1 as stated here has no goodness hypothesis on `T`.
This module neither proves H1 nor uses that literature result.

Once H1 is proved, the target follows by applying
`spaceAnalytificationMorphismStatement_of_etaleDescent`.
