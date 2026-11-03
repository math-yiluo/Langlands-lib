# Support-theory targets on the actual rational-point smooth category

Author: Worker 379. The nine propositions in
`Langlands.Aubert.General.RationalPointFamily` restate the generic targets of
`SupportCategoryStatements` for the actual group of rational points of a
connected reductive group and its actual standard subgroup families. They are
proposition definitions only: no instance of any target is proved here, and
nothing is assumed about the truth of the generic targets.

## Setting

Each statement quantifies over every field `k` with `IsNonarchimedeanLocalField`,
every connected reductive group scheme `G` over `Spec k` (`hG`), every actual
maximal split torus `i : T.toGrp ⟶ G` (`hi`) and every generic cocharacter `ν`
(`hν`). No split, quasisplit, positive-rank or characteristic-zero hypothesis is
imposed, and the empty simple-root set is allowed. The ambient group is
literally `RationalPoint k G.X` with the explicitly installed evaluation
topology `pointTopology`; its local compactness, nonarchimedean group structure
and Hausdorffness are explicit premises.

The subgroup families are literally the published `parabolic i ν`, `levi i ν`
and `unipotent i ν` at `rootSet i ν I`, indexed by finite sets of the actual
simple relative roots `SimpleRoot i ν`. Their finite enumeration is
`simpleRelativeRootFintype`, obtained from `HasRelativeRootSystem i` (`hRoots`)
and splitness of the torus. No arbitrary subgroup family, decomposition or
support relation is quantified. Representations have carriers in
`Type (max (u + 1) v)`: the generic targets are instantiated at universes
`.{u, u, max (u + 1) v}`, as in the other published rational-point targets.

## Derived generic arguments

The arguments of the generic targets are derived from named structural
inputs through published adapters, not taken as free fields:

| Generic argument | Actual value |
| --- | --- |
| `h` (ambient decompositions `P_I = L_I ⋉ U_I`) | `isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν` |
| `hL` (inside-Levi decompositions) | `isSemidirectDecomposition_in_levi i ν hInter hG hi hν` |
| `hU`, `hM` (closedness of radicals and Levis) | explicit premises `hU`, `hM` |
| `IsAssociate` | `rootAssociation i ν hN hZ` |

`hStandard : StandardCocharacterStatement` and
`hInter : StandardLeviIntersectionStatement` are the named structural inputs.
`rootAssociation i ν hN hZ I J n` (from `RationalStandardComplex`) requires the
actual point `n` to normalize the torus points. It also requires the image of
`rootSet i ν I` under the actual character action `weylCharacterAction` of the
class of `n` to be exactly `rootSet i ν J`. That action is transported through
the exact scheme/point normalizer and full-centralizer comparisons `hN` and
`hZ`. This is the erratum's condition `v(I) ⊂ S ∩ Φ⁺` (p. 4687) with
`v(I) = J`. Wherever a generic target uses `IsAssociate I J n`, it pairs it
with the Levi condition for the same `n`, `M J = n (M I) n⁻¹`, written
`∀ x, x ∈ M J ↔ n⁻¹ * x * n ∈ M I`. This holds both inside
`IsInSupportCategory` and in the target's own hypotheses and conclusions.
So the association is never a bare relabelling of root subsets.

Each definition keeps only the structural inputs its generic target uses.
None of the nine uses `StandardParabolicOrderStatement`,
`StandardParabolicEndpointsStatement` or the compact-limit property of the
radicals, so these are absent. `RationalCuspidalSeriesExistenceStatement` also
omits `hN` and `hZ`, because it involves no association. Leaving out an unused
premise only strengthens a universally quantified statement.

## Targets

| Declaration | Generic target | Source |
| --- | --- | --- |
| `RationalCuspidalSeriesExistenceStatement` | `CuspidalSeriesExistenceTarget` | Renard, Corollaire VI.2.1, p. 139 |
| `RationalCuspidalSupportAssociationStatement` | `CuspidalSupportAssociationTarget` | Renard, Théorème VI.5.4, (iv) ⇒ (i), pp. 173–174 |
| `RationalSupportCategoryAssociationInvarianceStatement` | `SupportCategoryAssociationInvarianceTarget` | erratum, p. 4687 (parenthesis after the definition of `Alg({I})`) |
| `RationalSupportCategoryIrreducibleJacquetDetectionStatement` | `SupportCategoryIrreducibleJacquetDetectionTarget` | proof of Renard VI.5.4, pp. 173–174 |
| `RationalSupportCategoryZeroDetectionStatement` | `SupportCategoryZeroDetectionTarget` | erratum, p. 4687, first sentence of the proof |
| `RationalSupportCategoryExactnessDetectionStatement` | `SupportCategoryExactnessDetectionTarget` | erratum, p. 4687, first sentence of the proof |
| `RationalSupportCategoryInductionJacquetStatement` | `SupportCategoryInductionJacquetTarget` | Renard, Théorème VI.7.2, p. 182, and Proposition VI.7.3, p. 185 |
| `RationalSupportCategoryJacquetVanishingStatement` | `SupportCategoryJacquetVanishingTarget` | Renard, Proposition VI.5.3 (i), p. 173, and VI.7.3 |
| `RationalSupportCategoryDecompositionStatement` | `SupportCategoryDecompositionTarget` | Renard, Théorème VI.7.2, p. 182 |

Page numbers are printed pages; the Renard PDF page is the printed page plus 6.
The exact formulation of each generic target, the convention that Aubert's
"cuspidale" is Renard's "supercuspidale", and the grouping of Bernstein
components by association class are explained in
`SupportCategoryStatements.md`. With the substitutions above, every target is
about the actual support category `Alg({I})` of the rational points
(`IsInSupportCategory` of `SupportCategory`), the actual normalized Jacquet
functors and the actual normalized induction.

## Provenance

This is a derived specialization: the mathematical content is that of the
cited Renard and erratum statements. The derivation pins the generic
parameters to the actual families and named structural inputs above. The
structural inputs, closedness premises and topological premises remain
intermediate obligations, to be discharged or matched to the parent's
external structural ledger. No representation-theoretic statement is moved
into them.
