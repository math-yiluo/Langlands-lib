# Proof: centralizers of tori in reductive group schemes are reductive

Worker 286.

`Langlands.GroupScheme.relativeTorusCentralizerReductive.{u}` proves exactly
`Langlands.GroupScheme.RelativeTorusCentralizerReductiveStatement.{u}`, published in
[`Torus.RelativeCentralizerReductiveStatement`](RelativeCentralizerReductiveStatement.md).
Its type has no added hypotheses. The proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

For a scheme `S`, a reductive group scheme `G` over `S`, a commutative group scheme `T`
with `RelativeTorus.IsTorus T.toGrp` and a homomorphism `t : T.toGrp ⟶ G`, the proof shows:

1. the centralizer `torusCentralizer t` is represented by a closed subgroup scheme of `G`;
2. every group scheme `Z` with a homomorphism `z : Z ⟶ G` representing
   `torusCentralizer t` satisfies `IsReductive Z`.

The hypothesis `IsClosedSubgroup t` of the statement is not used: the argument works for
any homomorphism from a relative torus.

## Declarations in this module

- `RelativeTorus.IsTorus.isSplitTorus_of_isAlgClosed`: a relative torus over an
  algebraically closed field `k` is split. The comparison
  `RelativeTorus.IsTorus.isTorus` (in
  [`Torus.RelativeFieldComparison`](RelativeFieldComparison.md)) turns it into a field
  torus. The published theorem
  `SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites` (in
  [`Torus.SplittingAssembly`](SplittingAssembly.md)), with its input discharged by the
  published proof `CoalgebraDescent.separablyClosedGroupLikeSpanning`, says that a field
  torus over a separably closed field is split. An algebraically closed field is
  separably closed.
- `isPseudoReductive_geometricFiber_of_torusCentralizer`: under the hypotheses above,
  for every representative `z : Z ⟶ G` of `torusCentralizer t` and every point `s ∈ S`,
  the geometric fibre `geometricFiber Z s` is pseudo-reductive. This is the
  geometric-fibre field of `IsReductive Z`.
- `relativeTorusCentralizerReductive`: the target theorem.

## The proof

**Existence and smoothness.** The published theorem
`relativeTorusCentralizer_hasSmoothClosedRepresentative` (in
[`Torus.RelativeCentralizerDescent`](RelativeCentralizerDescent.md)) applies because `G`
is affine and smooth over `S` (the first two fields of `IsReductive G`). It gives a group
scheme `C` and a homomorphism `c : C ⟶ G` that is a closed immersion, with `C → S` smooth,
representing `torusCentralizer t`. This is assertion 1. That theorem descends the
published smooth closed representability of split-torus centralizers over affine bases
along an affine open cover and then along the étale splitting cover of `T`.

**Smoothness and affineness of an arbitrary representative.** Let `z : Z ⟶ G` represent
`torusCentralizer t`. The published `SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy`
gives an isomorphism of group schemes `Z ≅ C` over `S`. Smoothness of `Z → S` follows from
smoothness of `C → S` by `smooth_of_over_iso`. The structure morphism of `C` is the closed
immersion `c` followed by the affine morphism `G → S`, so `C → S` is affine
(`IsClosedSubgroup.isAffineHom`), and affineness of `Z → S` follows by
`isAffineHom_of_over_iso`.

**Geometric fibres.** Fix `s ∈ S` and let `b : Spec K ⟶ S` be the geometric point
`geometricPoint S s`, where `K` is the algebraic closure of the residue field `κ(s)`.

- The geometric fibre `geometricFiber G s` is pseudo-reductive because `G` is reductive.
  Over the algebraically closed field `K` this gives `IsConnectedReductive`, by the
  published `IsPseudoReductive.isConnectedReductive_of_isAlgClosed`.
- The base change of `T` along `b` is again a relative torus (`RelativeTorus.IsTorus.baseChange`), so it
  is split by `RelativeTorus.IsTorus.isSplitTorus_of_isAlgClosed`.
- The base change of `z` along `b` represents the base change of the subgroup functor
  (`SubgroupFunctor.IsRepresentedBy.baseChange`). By the published
  `torusCentralizer_baseChange`, this base-changed functor is the centralizer of the
  base-changed homomorphism `t_K : T_K ⟶ G_K`.
- The published field theorem `splitTorusCentralizerReductive` (which proves
  `SplitTorusCentralizerReductiveStatement`, in
  [`Rational.SplitTorusCentralizerReductiveProof`](../Rational/SplitTorusCentralizerReductiveProof.md))
  now says that `geometricFiber Z s`, the base change of `Z` along `b`, is connected
  reductive. `IsConnectedReductive.isPseudoReductive` gives the required
  pseudo-reductivity.

Together these give `IsReductive Z`, which is assertion 2.

## Comparison with the source

The statement follows Brian Conrad, *Reductive group schemes* (2014), p.83, paragraph
before Remark 3.1.5 (registered as `conrad-2014-reductive-group-schemes`). Conrad obtains
smoothness of `Z_G(T)` from Lemma 2.2.4 and connected reductivity of its geometric fibres
from the classical theory (Borel, 13.17, Corollary 2). The Lean proof follows the same
outline. Existence and smoothness come from the Library's étale-descent construction
instead of the Hom-scheme argument of Lemma 2.2.4. On each geometric fibre the classical
fact is the Library's split-torus centralizer theorem, applied after splitting the torus
over the algebraically closed field.

This is a derived proof assembling published Library results. It does not change the
target statement or any module the statement imports.
