# Representation-theoretic prerequisite targets for the general Aubert adapters

Statements and bridge: Worker 1180 (task
`593ef603-6672-4424-976c-14e11e920d9c`). The adapters they serve,
[`Aubert.General.Parabolic`](Parabolic.md),
[`Aubert.General.AlternatingOperator`](AlternatingOperator.md) and
[`Aubert.General.DynamicParabolic`](DynamicParabolic.md), are Worker 23's.

This module states, as closed propositions, the representation-theoretic facts
that the general adapters take as named hypotheses: finite length of normalized
parabolic induction and Jacquet restriction, admissibility of finite-length
representations, and finite length of smooth contragredients. It neither assumes
nor proves any of them. It also proves one small bridge that turns the
finite-length targets into the adapters' hypothesis `ParabolicFiniteLength`.

## Setting

Every statement begins with the same binders:

* a field `F : Type u` with `[ValuativeRel F] [TopologicalSpace F]` and Mathlib's
  `[IsNonarchimedeanLocalField F]`, so `F` is a nonarchimedean local field with
  its valuation topology;
* a group scheme `G : GroupScheme (Spec (CommRingCat.of F))` and
  `hG : IsConnectedReductive G` (published `GroupScheme.Reductive.Basic`);
* for the Levi and parabolic statements, a cocharacter
  `χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G`.

The group `G(F)` is the actual type of rational points
`RationalPoint F G.X = (Over.mk (𝟙 (Spec F)) ⟶ G.X)`, the points tested by the
identity of `Spec F`, with its group structure from the group object `G`. Its
topology is pinned inside each statement by
`letI := rationalPointTopology F G.X`. That is the Conrad evaluation topology
(Conrad, Proposition 2.1), transported to the identity-test carrier by
`PointTopology.RationalPoints`. The topology needs `IsAffine G.X.left`, which each
statement obtains from the field `hG.isAffineHom` by
`isAffine_of_isAffineHom`. The same field gives `IsSeparated G.X.hom` through the
instance `IsSeparated.of_isAffineHom`, which `dynamic_isSemidirectDecomposition`
requires.

The subgroups are the published dynamic subgroups at the identity test object
`T = Over.mk (𝟙 (Spec (CommRingCat.of F)))`:

* `P(χ)(F) = (Dynamic.parabolic χ).carrier T`;
* `Z(χ)(F) = (Dynamic.centralizer χ).carrier T`;
* `U(χ)(F) = (Dynamic.unipotent χ).carrier T`.

Each is an actual subgroup of `G(F)`, and a representation of `Z(χ)(F)` is a
representation of that subgroup with the subspace topology.
`dynamic_isSemidirectDecomposition χ T` is the decomposition
`P(χ)(F) = Z(χ)(F) ⋉ U(χ)(F)`. The functors in the statements are Worker 23's
`normalizedInductionFunctor` and `jacquetFunctor` of that decomposition.

For connected reductive `G`, the subgroups `P_G(χ)` are exactly the parabolic
`F`-subgroups (Conrad–Gabber–Prasad, Proposition 2.2.9). Their unipotent radical
is `U_G(χ)` (CGP, Corollary 2.2.5), and `Z_G(χ)` is a Levi factor by the
semidirect decomposition (CGP, Proposition 2.1.8(2)). So quantifying over all
cocharacters `χ` covers every parabolic subgroup of Renard's statements, each
with a Levi decomposition.

## Hypotheses

The topology is fixed. These statements never take a topology on `G(F)` as a
hypothesis: with an arbitrary topology, for example the discrete one, the
targets are false. Only properties of the pinned topology appear as hypotheses,
and only where a functor or a construction needs them to typecheck:

* `[IsTopologicalGroup (RationalPoint F G.X)]` in the two contragredient
  statements, because the published `SmoothRep.contragredient` requires it;
* `[LocallyCompactSpace (RationalPoint F G.X)]`,
  `[NonarchimedeanGroup (RationalPoint F G.X)]` and
  `hU : IsClosed U(χ)(F)` in the two functor statements, because the functors
  are defined only under these.

For a nonarchimedean local field all of these are true. By Conrad, Proposition
2.1, `G(F)` is a locally compact Hausdorff topological group, and the closed
subgroup scheme `U_G(χ)` has closed points `U(χ)(F)`. By Renard V.2.1, `G(F)` is
totally disconnected, and its compact open subgroups form a basis of
neighbourhoods of `1`. They are properties of the one pinned topology,
not alternative topologies. Proving them belongs to Conrad's point-topology task
`886bf565`, not to this module.

## The targets

Throughout, `SmoothRep.{0, u, uV} ℂ H` is the category of smooth complex
representations of `H` with carriers in `Type uV`. `HasFiniteLength` is finite
length over the group algebra. `IsAdmissible` means finite-dimensional fixed
vectors under every open subgroup, as in Renard III.1.7.

* `RationalPointsFiniteLengthAdmissibleStatement`: every finite-length smooth
  complex representation of `G(F)` is admissible. This is the direction "finite
  length ⇒ admissible" of Howe's theorem (Renard VI.6.3, printed pp. 178–179).
  Renard's proof inducts on length, starting from VI.2.2 (irreducible ⇒
  admissible, printed p. 140).
* `DynamicLeviFiniteLengthAdmissibleStatement`: the same for `Z(χ)(F)`, for every
  `χ`.
* `RationalPointsContragredientFiniteLengthStatement`, assuming
  `[IsTopologicalGroup]`: Worker 23's `ContragredientPreservesFiniteLength`
  holds for `G(F)`. That is, the smooth contragredient of every finite-length
  smooth complex representation has finite length.
* `DynamicLeviContragredientFiniteLengthStatement`: the same for `Z(χ)(F)`.
* `DynamicInductionFiniteLengthStatement`, assuming `[LocallyCompactSpace]`,
  `[NonarchimedeanGroup]` and `hU`:
  `PreservesFiniteLength (normalizedInductionFunctor (dynamic_isSemidirectDecomposition χ T) hU)`.
  So normalized parabolic induction `SmoothRep ℂ Z(χ)(F) ⥤ SmoothRep ℂ G(F)` sends
  finite-length representations to finite-length representations (Renard VI.6.2,
  printed p. 178). Renard's Lemme covers an irreducible inducing representation.
  The opening paragraph of VI.6.2 states the conclusion for finite length, which
  follows from the Lemme by exactness of induction and induction on length.
* `DynamicJacquetFiniteLengthStatement`, with the same hypotheses:
  `PreservesFiniteLength (jacquetFunctor (dynamic_isSemidirectDecomposition χ T) hU)`.
  So normalized Jacquet restriction `SmoothRep ℂ G(F) ⥤ SmoothRep ℂ Z(χ)(F)` sends
  finite-length representations to finite-length representations (Renard VI.6.4,
  printed p. 179, from VI.6.3, VI.1.3 and the Corollaire of VI.6.1, printed
  p. 176).

## Proved bridge

`rational_parabolicFiniteLength` takes the two functor targets, together with
`[LocallyCompactSpace]`, `[NonarchimedeanGroup]` and `[T2Space]` for `G(F)`,
`hU`, closedness of `P(χ)(F)`, continuity of the decomposition's projection
`P(χ)(F) →* Z(χ)(F)`, and `Jacquet.Localization.IsLimitOfCompactSubgroups U(χ)(F)`.
It concludes `ParabolicFiniteLength (dynamic_isSemidirectDecomposition χ T) hU`.
The proof applies Worker 23's `ParabolicFiniteLength.of_preservesFiniteLength`.
Compact-open cofinality comes from Worker 23's
`compactOpenCofinal_of_nonarchimedean` (local compactness and the nonarchimedean
property), and the two finite-length conjuncts come from the targets.

The extra structural hypotheses are those of Worker 23's exactness theorems. They
are true for the pinned topology, but nothing here proves them. Hausdorffness and
closedness come from Conrad, Proposition 2.1: closed immersions give closed
embeddings when `F` is Hausdorff. The projection is the published
`Dynamic.limitHom` (`dynamic_projection_eq_limitHom`). That is the map on points
of the projection `P_G(χ) → Z_G(χ)` of CGP Lemma 2.1.5 and Proposition 2.1.8(2),
and Conrad's topology is functorial, so the projection is continuous. That
`U(χ)(F)` is a limit of compact subgroups is Renard V.5.2(iii), routed through
Worker 6's task `15df7cd7`.

## Provenance and scope

* The admissibility and functor targets are stated in Renard for `G = G(F)` and
  every parabolic `P = MN`. The Levi targets apply the same theorems to the
  connected reductive group `Z_G(χ)`. Renard V.2.1 says the topology of the
  rational points does not depend on the embedding, so the subspace topology on
  `Z(χ)(F) ⊂ G(F)` is its own topology. The Levi statements need only this
  subgroup form. Identifying `Z_G(χ)` with a connected reductive group scheme in
  the Library, so that the `G`-level statements apply to it directly, is
  structural work owned by the algebraic-groups tasks (`2b5e4a00`, `8ace819d`).
  It is not done here.
* The contragredient targets are derived; Renard does not state them as one
  result. A finite-length representation has admissible irreducible
  subquotients (VI.6.3, VI.2.2). The smooth dual is exact (I.4.1 Lemme, printed
  p. 23, read through III.1.6, printed p. 61). The contragredient of an admissible
  simple module is simple (I.5.1 Corollaire, printed p. 26, translated in
  III.1.7, printed p. 62). Induction on length then gives finite length of the
  contragredient.
* Normalization. Renard VI.1.2 (printed pp. 135–136) writes
  `i^G_P(τ) = Ind^G_P(τ ⊗ δ_P^{-1/2})` and `r^G_P(π) = π_N ⊗ δ_P^{1/2}` with his
  inverted `δ_P`. Worker 23's induction functor twists by the half modulus of
  conjugation on `U`, evaluated on all of `P`. Bernstein–Zelevinsky 1977
  §1.8(a)(1) and Renard instead use the Levi half modulus inflated to `P`. The two
  characters agree only when `U` is unimodular (`IsUnimodularModulus U hU`; see
  `closedHalfCharacter_eq_comp_projection` and [`Parabolic.md`](Parabolic.md)).
  Unimodularity holds whenever `U` is a limit of compact subgroups
  (`isUnimodularModulus_of_isLimitOfCompactSubgroups`). For `U(χ)(F)` that is
  Renard V.5.2(iii), printed p. 123, which is the same input the bridge above
  takes and which is not proved here. When `U` is unimodular, the functors here and
  Renard's differ only by twisting by a character of the Levi subgroup. Such a twist is an
  autoequivalence of the smooth category that preserves finite length, so then the
  finite-length targets mean the same thing in either convention.
* Conditional status. Everything here is a target or a conditional bridge.
  Nothing proves Renard's theorems, and nothing completes the parent program
  `46df6a68`.
* Not stated here: transitivity of induction (Renard VI.1.4), the geometric lemma
  (VI.5.1) and second adjointness (VI.9.6). Each needs composite-parabolic or
  double-coset structural data that the Library does not yet have. The joint
  adapter table lists them with their existing owners. Compatibility of the
  functors with conjugation is an intrinsic law of the generic adapter layer,
  which Worker 23 treats within this task, so it is not a target here.

## Sources

* D. Renard, *Représentations des groupes réductifs p-adiques* (2026 version),
  `renard-2026-representations-groupes-reductifs-padiques` (PDF page = printed
  page + 6): VI.6.1 Corollaire p. 176; VI.6.2 Lemme p. 178; VI.6.3 Théorème
  pp. 178–179 and VI.2.2 p. 140; VI.6.4 p. 179; VI.1.2 pp. 135–136; I.4.1 Lemme
  p. 23; I.5.1 Corollaire p. 26; III.1.6 p. 61; III.1.7 p. 62; V.2.1 p. 104;
  V.5.2(iii) p. 123.
* B. Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
  `conrad-2011-weil-grothendieck-adelic-points`: Proposition 2.1 and its proof,
  printed pp. 2–3 (the pinned topology and its properties).
* B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*, 2nd ed. (2015),
  `conrad-gabber-prasad-2015-pseudo-reductive`: Lemma 2.1.5 and Proposition
  2.1.8(2), printed p. 53 (as cited by the published `Dynamic` modules); Corollary 2.2.5,
  printed p. 64; Proposition 2.2.9, printed p. 67.
