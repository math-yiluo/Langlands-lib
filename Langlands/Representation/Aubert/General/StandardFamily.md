# The actual standard family as semidirect decompositions

Implementation and documentation: Worker 23 (task
`593ef603-6672-4424-976c-14e11e920d9c`, the initial adapter unit of the general
Aubert program `46df6a68-5db4-4428-8044-05151d6ce1f6`).

This module connects the published actual standard family of
[`Aubert.General.RationalPointFamily`](RationalPointFamily.md) to the semidirect
decomposition predicate of [`Aubert.General.Parabolic`](Parabolic.md). The
normalized functors, their K0 maps and `alternatingOperator` can then be applied
to the actual standard parabolics `P_I(k) = L_I(k) ⋉ U_I(k)`. **The result is
conditional** on the published Prop target
`GroupScheme.StandardCocharacterStatement` (task `8ace819d`). This target is
taken as the explicit hypothesis `hstd`, and nothing here proves it.

## Setting

`k` is a field, `G` a group scheme over `Spec k` with
`hG : IsConnectedReductive G`, `i : T ⟶ G` a homomorphism from a split torus with
`hi : IsMaximalSplitTorus i`, and `ν` a cocharacter with
`hν : IsGenericCocharacter i ν`. The index type is the published
`SimpleRoot i ν`, the actual simple relative roots positive for `ν`. For
`I : Finset (SimpleRoot i ν)`, the published `parabolic i ν I`, `levi i ν I` and
`unipotent i ν I` are the identity-test rational points of
`standardParabolic/standardLevi/standardUnipotent i ν (rootSet i ν I)`. These
are the choice-free intersections over all standard cocharacters of `rootSet i ν
I` of the corresponding dynamic subgroups. The instance argument
`[IsAffineHom G.X.hom]` is the one the published family uses. It agrees, as a
proposition, with the one `hG.isAffineHom` provides inside the target.

## Declarations

Namespace `Langlands.Aubert.General.RationalPointFamily`.

* `exists_standardCocharacter_eq hstd hG i hi ν hν I` gives a standard
  cocharacter `ζ` of `rootSet i ν I` such that `parabolic i ν I`, `levi i ν I`
  and `unipotent i ν I` equal the rational points of `Dynamic.parabolic`,
  `Dynamic.centralizer` and `Dynamic.unipotent` of `groupHom ζ ≫ i`. The proof
  applies `hstd` to `rootSet i ν I`, which lies in the simple roots by
  `rootSet_subset`. The target supplies existence of `ζ` and the three equalities
  of subgroup functors, which are then evaluated at the identity test object.
* `isSemidirectDecomposition hstd hG i hi ν hν I` proves
  `IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I)`.
  It rewrites by the previous equalities and applies the published
  `dynamic_isSemidirectDecomposition`. The separatedness that lemma needs is the
  published `IsConnectedReductive.isSeparated`.

## Functors and operator for the standard family

This section takes the topology of `G(k)` as instance arguments
`[TopologicalSpace (RationalPoint k G.X)] [LocallyCompactSpace ..]
[NonarchimedeanGroup ..]`. The actual application binds the published
`rationalPointTopology`, equivalently `RationalPointFamily.pointTopology`, with
`letI`. Local compactness and nonarchimedeanness of that topology remain
hypotheses (the C1 input of the dependency note), as does closedness of the
unipotent points.

* `standardInductionFunctor hstd hG i hi ν hν I hU` is
  `normalizedInductionFunctor (isSemidirectDecomposition ..) hU`, normalized
  parabolic induction `SmoothRep ℂ L_I(k) ⥤ SmoothRep ℂ G(k)` from the actual
  standard Levi.
* `standardJacquetFunctor hstd hG i hi ν hν I hU` is
  `jacquetFunctor (isSemidirectDecomposition ..) hU`, normalized Jacquet
  restriction `SmoothRep ℂ G(k) ⥤ SmoothRep ℂ L_I(k)`.
* `standardAlternatingOperator hstd hG i hi ν hν hU hfl` is
  `alternatingOperator` for `P M U := parabolic i ν, levi i ν, unipotent i ν`
  and `h := isSemidirectDecomposition hstd hG i hi ν hν`. It needs
  `[Fintype (SimpleRoot i ν)]`, closedness `hU` of every `unipotent i ν I`, and
  the named finite-length hypotheses `hfl : ∀ I, ParabolicFiniteLength ..`. It
  is Aubert's unadjusted `D_G = ∑_{I ⊆ S} (-1)^{|I|} i_I ∘ r_I` (Définition 1.5)
  for the actual standard family. Its source identification with Aubert's
  normalized functors needs each `unipotent i ν I` to be unimodular; see "Source
  identification" in [`Parabolic.md`](Parabolic.md).
* `standardAlternatingOperator_eq` states, by `rfl`, that it is that instance
  of `alternatingOperator`. So `alternatingOperator_ofRepresentation` (the class
  formula) and `alternatingOperator_of_isEmpty` (no simple roots) apply to it.

All three definitions are conditional on `hstd` and on the stated hypotheses.
None of them proves a representation-theoretic statement.

## Sources

* D. Renard, *Représentations des groupes réductifs p-adiques* (2026 version),
  registered as `renard-2026-representations-groupes-reductifs-padiques`:
  V.3.1 (Levi decomposition `P = M N`, printed p. 110) and V.3.8 (standard
  parabolic subgroups, printed p. 111; printed = PDF − 6).
* A.-M. Aubert, *Dualité dans le groupe de Grothendieck de la catégorie des
  représentations lisses de longueur finie d'un groupe réductif p-adique*,
  Trans. AMS 347 (1995), registered as `aubert-1995-duality`: Définition 1.5,
  printed p. 2181.
* B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*, 2nd ed. (2015),
  registered as `conrad-gabber-prasad-2015-pseudo-reductive`: Proposition
  2.1.8(2) (printed p. 53), the dynamic decomposition `P(λ) = Z(λ) ⋉ U(λ)` used
  through `dynamic_isSemidirectDecomposition`.
