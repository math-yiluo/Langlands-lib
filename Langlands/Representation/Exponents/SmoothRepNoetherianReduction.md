# Noetherianity of `M(G)` from four explicit inputs

Worker 1582. A conditional reduction of Renard VI.7.5, Proposition, printed
page 186 / PDF page 192, in David Renard, *Représentations des groupes
réductifs p-adiques*, French version of 9 July 2026. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, at
`/home/taskhub/central-library/Renard--Representations des groupes
reductifs p-adiques (2026 version)--2026.pdf`.

The module proves the published `SmoothRepNoetherianCategoryStatement` from
four explicit hypotheses. None of them is proved here, so the exact
Proposition is **not** proved by this module. Two of the hypotheses are
published statements, and two are stated here.

Renard proves the Proposition with the faithful exact functor `R` of VI.7.2
into a product of supercuspidal blocks. The implemented proof follows a
different, derived route: strong induction on the Lie dimension of `G`. The
supercuspidal part of a representation and its Jacquet modules along finitely
many proper parabolics take the place of `R`.

## Statements

- `SupercuspidalFiniteTypeNoetherianStatement`: for every nonarchimedean local
  field `k`, every connected reductive `G` over `k` and every smooth complex
  representation `A` of `G(F)` (carrier universe `v`), if `A` is supercuspidal
  (the published `IsSupercuspidal`, tested on every proper actual rational
  parabolic) and `A` is finitely generated over `ℂ[G(F)]`, then `A` is a
  Noetherian `ℂ[G(F)]`-module. This is the first step of Renard's proof
  (printed page 186 / PDF page 192). There, a supercuspidal block
  `M(G)_[ρ]` is equivalent to modules over a Noetherian algebra by VI.4.4
  (from printed page 155 / PDF page 161), and a finite-type object has only
  finitely many nonzero block components. The two-factor and block
  decompositions are those of VI.3.5, printed pages 146–147 / PDF pages
  152–153. Here the conclusion is stated for supercuspidal representations
  directly, without the block decomposition.
- `FiniteProperParabolicSupercuspidalTestStatement`: for every such `k` and
  `G`, there are a natural number `n` and `n` actual rational parabolic data
  `D i : ParabolicDatum G`, each with `¬ IsIso (D i).p`, with the following
  property. Every smooth `A` whose published normalized `jacquetFunctor`
  modules along all `D i` are `Subsingleton` is supercuspidal. This is a finite
  form of Renard VI.2.1, Remark 1, printed page 137 / PDF page 143: it suffices
  to test the proper standard parabolics, of which there are finitely many.
  The data are not required to be standard.
- `SmoothRepNoetherianAt k G hG`: the conclusion of the Proposition for one
  connected reductive group. Under the canonical point topology and for every
  local compactness and nonarchimedean instance, it says the published
  `Langlands.Renard.IsNoetherianCategory` of `SmoothRep ℂ G(F)`. Unfolded at
  every `k` and `G`, it is exactly the published Proposition.

The two published inputs are `LeviJacquetFiniteTypeStatement` (Renard VI.1.3,
Proposition, printed page 136 / PDF page 142: normalized Jacquet modules,
transported to the Levi points, of finite-type representations are of finite
type) and `RepresentedCuspidalRemainderSplittingStatement` (the objectwise
cuspidal/remainder splitting consequence of VI.3.5).

## Implemented proofs

`lieDimension_levi_lt` assumes `G` connected reductive, `p : P ⟶ G` a
parabolic and `l : M ⟶ P` a rational Levi, with `p` not an isomorphism. It
proves that the Lie dimension of `M` is strictly smaller than that of `G`. The
composite `l ≫ p` is a closed subgroup by the published
`IsClosedSubgroup.comp`. If it were an isomorphism, the published
`IsClosedSubgroup.isIso_of_isIso_comp` would make `p` one. The published
`Lie.dimension_lt_of_proper_closedSubgroup` then applies, using smoothness and
connectedness of `G` and smoothness of `M` from connected reductivity.

`leviJacquetFunctor_preservesMonomorphisms` assumes `G` connected reductive
and proves that the transported normalized Jacquet functor
`leviJacquetFunctor` preserves monomorphisms. A monomorphism `f` has
injective underlying map and, with its cokernel projection, forms an actual
short exact sequence (`SmoothRep.isShortExact_cokernelπ`). The published
exactness theorem `leviParabolicFunctorsExact` keeps the image short exact,
so the image of `f` is injective, hence a monomorphism.

For data `D : Fin n → ParabolicDatum G` and splittings
`hs : ∀ A, HasCuspidalRemainderSplitting A`, the finite family
`familyFunctor D hs` is indexed by `Option (Fin n)`. The index `none` gives
`cuspidalPartFunctor hs` of `RepresentedCuspidalProjection`, valued in smooth
representations of `G(F)`. The index `some i` gives `leviJacquetFunctor` along
`D i`, valued in smooth representations of the Levi points `M_i(F)` with their
canonical topology. The structure `PointGroup` bundles a group and a topology;
`pointGroups D` indexes these different target categories by it. Every member
preserves monomorphisms (`familyFunctor_preservesMonomorphisms`).

The family jointly reflects isomorphisms between monomorphisms when the `D i`
test supercuspidality (`familyFunctor_jointlyReflectsMonoIsos`). Let
`f : A ⟶ B` be a monomorphism sent to an isomorphism by every member, and let
`Q` be its cokernel.
- For each `i`, the image of the short exact sequence `A → B → Q` is short
  exact, and the image of `f` is surjective. Hence the image of the cokernel
  projection is zero and surjective, so the Jacquet module of `Q` along `D i`
  is `Subsingleton`. The test makes `Q` supercuspidal.
- The cuspidal part functor is additive. The image of the cokernel
  projection is therefore zero after cancelling the isomorphism image of
  `f`. It is also an epimorphism, so the supercuspidal part of `Q` is zero.
- A supercuspidal representation with zero supercuspidal part is zero
  (`isZero_of_isSupercuspidal_of_isZero_cuspidalPartFunctor_obj`). So `Q` is
  `Subsingleton`, `f` is surjective, hence an epimorphism, and an
  isomorphism in the abelian category.

`smoothRepNoetherianAt_of_levis` is the inductive step. It assumes the four
inputs and, for every proper parabolic of `G` with rational Levi `M`,
`SmoothRepNoetherianAt` for `M`. It concludes `SmoothRepNoetherianAt` for `G`.
Arbitrary subobject unions exist by `SmoothRep.hasAllSubobjectUnions` of
`RenardNoetherian`. Take `X` of finite type in Renard's sense;
by `SmoothRep.renardFiniteType_iff` it is finitely generated over `ℂ[G(F)]`.
The splitting input gives `hs`, and the test input gives `n`, `D` and the
test. `noetherianObject_of_finite_family` of `FiniteFamilyNoetherian` reduces
Noetherianity of `X` to that of its images under the family.
- The supercuspidal part of `X` is a quotient of `X` (through
  `cuspidalPartπ`), hence finitely generated, by Mathlib's
  `Module.Finite.of_surjective`. It is supercuspidal, so the first new input
  makes it Noetherian, and `SmoothRep.renardNoetherian_iff` converts.
- The Jacquet module of `X` along `D i` is finitely generated over
  `ℂ[M_i(F)]` by VI.1.3. It is therefore of finite type, hence Noetherian by
  the hypothesis for `M_i`, under the published local compactness and
  nonarchimedean instances of the Levi points.

`smoothRepNoetherianCategory_of_inputs` assumes the four inputs and proves the
exact `SmoothRepNoetherianCategoryStatement.{u, v}`. It proves
`SmoothRepNoetherianAt` for every `G` of Lie dimension `d`, by strong
induction on `d`. The step applies `smoothRepNoetherianAt_of_levis`, with the
induction hypothesis made available for Levis by `lieDimension_levi_lt`.

## Scope

All statements keep the full quantification of the published represented
statements: field universe `u` and carrier universe `v`, valuative
nonarchimedean local field with Hausdorff topology, actual connected
reductive `G`, canonical point topology, and arbitrary local compactness and
nonarchimedean instances. No admissibility, irreducibility, standardness or
finite-length hypothesis is added. The first new input is stated for
supercuspidal representations of every connected reductive group, and the
second only asks for some finite list of proper parabolic data. The proof uses
only the axioms `propext`, `Classical.choice` and `Quot.sound`. The module
imports the not yet published candidates `RepresentedCuspidalProjection`,
`RenardNoetherian` and `FiniteFamilyNoetherian` of the same task.
