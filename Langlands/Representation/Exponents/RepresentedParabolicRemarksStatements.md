# Two remarks on represented parabolics: Renard VI.1.1 and VI.2.1 (statements)

Module `Langlands.Representation.Exponents.RepresentedParabolicRemarksStatements`.
Namespace `Langlands.Aubert.General.RepresentedParabolic`.
Two Prop-valued definitions; nothing is proved here.

- `LeviUnnormalizedInductionRightAdjointStatement`: the unnormalized parabolic
  induction `Ind_P^G` has a right adjoint (VI.1.1, Remark, first sentence).
- `SupercuspidalStandardParabolicCriterionStatement`: supercuspidality may be
  tested on the proper standard parabolics only (VI.2.1, first Remarks,
  Remark 1).

Worker 4 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, after checking with Worker 1222 that
neither item was stated or in progress elsewhere.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both statements are source statements read on the cited pages.

VI.1.1, after the Theorem (`j_N` is left adjoint to `Ind_P^G`) and its
Corollary, printed p.135 / PDF p.141:

> **Remarque.** Il se trouve que `Ind_P^G` admet aussi un adjoint à droite.
> En effet, la variété `G/P` étant compacte, d'après le lemme III.2.3,
> `Ind_P^G = Ind_P^G ∘ F_P^M = ind_P^G ∘ F_P^M`.
> Or le foncteur d'oubli `F_P^M` admet un adjoint à droite, le foncteur
> `I_P^M`. D'autre part, `ind_P^G = P_P^G(• ⊗ δ_{P\G}^{-1})` d'après le
> théorème III.2.6 et `P_P^G` (resp. `• ⊗ δ_{P\G}^{-1}`) admet le
> pseudo-foncteur d'oubli `F̌_P^G` (resp. `• ⊗ δ_{P\G}`, cf. remarque
> III.1.15, 3) comme adjoint à droite. Par conséquent, `Ind_P^G` préserve les
> colimites.

VI.2.1, Definition and first block of Remarks, printed p.137 / PDF p.143:

> **Définition.** Une représentation lisse `(π, V)` de `G` est dite
> supercuspidale si pour tout sous-groupe parabolique propre `P = MN` de `G`,
> `r_P^G(V)` est nul.
>
> **Remarques.** 1. Une représentation lisse `(π, V)` de `G` est
> supercuspidale si pour tout sous-groupe parabolique propre standard
> `P = MN` de `G`, `r_P^G(V)` est nul.

"Standard" is defined in V.3.8, printed p.111 / PDF p.117: a maximal split
torus `A_∅` and a minimal parabolic `P_∅ = M_∅ N_∅` with `M_∅ = Z_G(A_∅)` are
fixed; a parabolic `P` is standard if `P_∅ ⊂ P`, and it then has a unique
Levi factor `M` containing `A_∅`, the standard Levi. V.3.9 (printed p.112 /
PDF p.118) states that every parabolic is conjugate to a standard one.

## Common data

Both statements quantify over the data of the published represented
interface (as in `LeviUnnormalizedParabolicStatements` and the published
`IsSupercuspidal`):

- a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local
  field of any characteristic;
- a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`, the
  affine structure `hG.isAffineHom`, the canonical topology
  `RationalPointFamily.pointTopology` on `rationalPoints G`, and the
  hypotheses `[LocallyCompactSpace (rationalPoints G)]` and
  `[NonarchimedeanGroup (rationalPoints G)]` for that topology.

An *actual rational parabolic triple* is `p : P ⟶ G`, `l : M ⟶ P`,
`r : U ⟶ P` with `hp : IsParabolicSubgroup p`,
`hl : IsRationalLeviSubgroup l`,
`hr : LeviSubgroup.IsGeometricUnipotentRadical r` and
`hmul : IsIso (subgroupMultiplication l r)`; it is the represented form of
Renard's `P = MN`. It is proper when `¬ IsIso p`.

## `LeviUnnormalizedInductionRightAdjointStatement`

For every actual rational parabolic triple, put on `rationalPoints M` the
topology `leviPointTopology l hl`, with local compactness and the
nonarchimedean-group property given by the published
`leviPoints_locallyCompactSpace` and `leviPoints_nonarchimedeanGroup`. Let
`h` be the published decomposition
`isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul` of
the parabolic image `P(F)` as the Levi image times the radical image. The
statement defines

`Ind := SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm ⋙ inflationFunctor h ⋙ Induction.smoothInductionFunctor (pointImage p)`

and asserts `Ind.IsLeftAdjoint`, i.e. there exist a functor `R` and an
adjunction `Ind ⊣ R` (Mathlib's `Functor.IsLeftAdjoint`).

`Ind` is exactly the unnormalized induction of the published
`LeviUnnormalizedParabolicStatements`: a smooth representation `σ` of `M(F)`
is pulled back to the Levi image along `leviPointsEquiv p l hp hl`, inflated
to `P(F)` along the Levi projection (Renard's trivial extension
`τ(mn) = τ(m)`), and smoothly induced to `G(F)` with no normalizing
character.

**Universes.** Both categories have carriers in the universe `max u v`:
`Ind : SmoothRep.{0, u, max u v} ℂ (rationalPoints M) ⥤ SmoothRep.{0, u, max u v} ℂ (rationalPoints G)`.
Smooth induction raises a carrier universe `w` to `max u w`; the statement
takes `w = max u v`, so source and target live in one universe, and the
categorical adjunction is stated between them. The statement thus covers every carrier
universe containing the field's universe `u` (for `k : Type`, every carrier
universe). The mixed-universe functor
`SmoothRep.{0, u, v} … ⥤ SmoothRep.{0, u, max u v} …` of the published
statements is not used here: a right adjoint of it would have to produce
`v`-small representations from arbitrary `max u v`-small ones, which is not
the source's construction.

**Relation to the published statements.** The published
`LeviUnnormalizedFunctorsPreserveLimitsStatement` already states (and
`leviUnnormalizedFunctorsPreserveLimits` proves) the Remark's conclusion,
that `Ind` preserves colimits of `Type v`-indexed diagrams; its Markdown
records that the Remark's first sentence, the existence of a right adjoint,
was not stated. This statement supplies it. By Mathlib's
`Functor.IsLeftAdjoint` API it implies colimit preservation of every size for
the common-universe `Ind`.

**Why it is true; possible proof routes.** The source's route: `G/P` is
compact (III.2.3), so smooth induction equals compact induction; the
forgetful functor `M(M) → M(P)` (inflation) has the right adjoint `I_P^M`;
compact induction is `P_P^G(• ⊗ δ_{P\G}^{-1})` (III.2.6); `P_P^G` has the
pseudo-forgetful functor as right adjoint and the twist has the inverse twist
as right adjoint (III.1.15, Remark 3). None of `I_P^M`, `P_P^G` or the
pseudo-forgetful functor is a published functor on this interface. An
alternative route is Mathlib's special adjoint functor theorem
`isLeftAdjoint_of_preservesColimits_of_isSeparating`: the category of smooth
representations of `M(F)` in the common universe `w = max u v` is
cocomplete, locally small and well-copowered, it has the small separating
family of compactly induced representations `ind_K^M 1` for the compact open
subgroups `K` (their homomorphisms into `σ` are the vectors of `σ^K`), and
`Ind` preserves colimits. The published colimit preservation
(`leviUnnormalizedFunctorsPreserveLimits`) is for the mixed-universe functor
and `Type v`-sized diagrams, so it would have to be redone for size `w`.

## `SupercuspidalStandardParabolicCriterionStatement`

Additional data: a commutative group scheme `T` over `Spec k`, a map
`i : T.toGrp ⟶ G` with `IsMaximalSplitTorus i`, and a cocharacter `ν` with
`IsGenericCocharacter i ν` (`ν` pairs nontrivially with every relative
root). These fix the standard family: the simple relative roots
`Δ = simpleRelativeRoots i ν` (positive relative roots, pairing positively
with `ν`, that are not sums of two positive relative roots) and, for every
`J ⊆ Δ`, the published standard parabolic and Levi subgroup functors
`standardParabolic i ν J` and `standardLevi i ν J`.

For every smooth representation `A : SmoothRep.{0, u, v} ℂ (rationalPoints G)`
(independent carrier universe `v`) the statement asserts

`IsSupercuspidal A ↔ ∀ (actual rational parabolic triple p, l, r) (J ⊆ Δ),
SubgroupFunctor.range p = standardParabolic i ν J →
SubgroupFunctor.range (l ≫ p) = standardLevi i ν J →
¬ IsIso p → Subsingleton ((jacquetFunctor p l r hp hr hl hmul).obj A)`.

Here `IsSupercuspidal A` is the published definition (Renard's VI.2.1
Definition): `Subsingleton ((jacquetFunctor p l r hp hr hl hmul).obj A)` for
every proper actual rational parabolic triple, where `jacquetFunctor` is the
published normalized Jacquet functor `r_P^G` along the radical image
`pointImage (r ≫ p)` with values in representations of the Levi image.
`Subsingleton` of the Jacquet module is "`r_P^G(V)` est nul". The right-hand
side is the same test restricted to the proper triples whose parabolic and
Levi are standard.

**Encoding of "standard".** Renard's standard `P = MN` (`P ⊃ P_∅`, `M` the
Levi containing `A_∅`) is encoded through simple-root subsets: the triple's
parabolic and Levi, as subgroup functors (equalities on every test scheme),
are `standardParabolic i ν J` and `standardLevi i ν J` for some `J ⊆ Δ`. This
is the Borel–Tits description of the parabolics containing a minimal
parabolic and of their Levi factors containing the maximal split torus, and
it is the encoding used by the published
`NormalizedTemperedStandardReductionStatement` and
`ArbitraryParabolicTemperedConjugation`. The published intersections
`standardParabolic` and `standardLevi` are over standard cocharacters; the
published and proved `StandardCocharacterStatement` (`standardCocharacter`)
gives, for maximal split `i`, generic `ν` and `J ⊆ Δ`, a standard cocharacter
`ζ` and the equalities `standardParabolic i ν J = Dynamic.parabolic (ζ ≫ i)`
and `standardLevi i ν J = Dynamic.centralizer (ζ ≫ i)`. So no index `J` has
an empty intersection, and the tests are on actual standard parabolics and
their standard Levis. Unlike the published tempered reduction, no explicit
cocharacter `ζ` is carried in the tests: with this structural theorem
available, it would add nothing.

No hypothesis that `Dynamic.parabolic (ν ≫ i)` is a minimal parabolic is
added. The left-hand side does not depend on `(i, ν)`; the statement claims
that the tests attached to every maximal split torus and generic cocharacter
suffice, as in the published conditional comparison
`isSupercuspidal_iff_isCuspidal`, which likewise assumes only that `i` is
maximal split and `ν` generic (besides structural statements), with no
minimality hypothesis.

**Direction of the content.** The forward implication is immediate: the
standard tests are among the tests of `IsSupercuspidal`. The source's
Remark is the converse. The converse is not weakened: every standard triple
satisfying the range equalities is tested, and `J` ranges over all subsets
of `Δ`, the proper ones being selected by `¬ IsIso p`.

**Why it is true; proof route in the Library.** Every proper parabolic is
`G(F)`-conjugate to a proper standard one, with its Levi carried to the
standard Levi (V.3.9), and conjugation transports the Jacquet modules. In
the Library, `RepresentedCuspidalityComparison` proves
`isSupercuspidal_of_isCuspidal`: vanishing along the radical images of the
actual standard family `unipotent i ν I` implies `IsSupercuspidal A`, via
`properParabolicUnipotentStandardization` and
`coinvariantsTranslateEquiv`, assuming `ParabolicDynamicStatement` and
`SmoothMaximalSplitTorusConjugacyStatement` (both now proved:
`parabolicDynamic`, `smoothMaximalSplitTorusConjugacy`), a relative root
system (`relativeRootSystem`) and closedness of the standard radical images.
`RepresentedStandardCuspidality` (`standard_representatives_geometric_of_standardCocharacter`)
exhibits the standard members `Standard.parabolicHom i ν _` etc. as actual
rational parabolic triples. A proof of this statement assembles these: it
must show that those standard representatives satisfy the two range
equalities for the corresponding `J`, so that the right-hand side applies to
them, and discharge the closedness and finiteness side conditions from the
represented structure.

**Not stated.** Remark 2 of VI.2.1 (subquotients of supercuspidal
representations are supercuspidal) is not part of this unit.

## Formalization choices

- The common universe `max u v` in `LeviUnnormalizedInductionRightAdjointStatement`,
  explained above.
- The represented triple `(p, l, r)` with `hmul` for `P = MN`, as everywhere in
  this interface; `r_P^G` is the published normalized `jacquetFunctor`.
- "Standard" through `J ⊆ simpleRelativeRoots i ν` and range equalities of
  subgroup functors (derived from V.3.8 via the Borel–Tits description),
  with the standard family fixed by an arbitrary maximal split torus and
  generic cocharacter.
- Minimal hypotheses: no admissibility, finite length or irreducibility of
  the representations; arbitrary characteristic and nonsplit `G` are
  included.
