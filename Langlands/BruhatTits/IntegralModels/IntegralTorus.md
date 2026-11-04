# Integral tori in supplied Bruhat–Tits models

This definition unit expands the torus and simply connected clauses of Kaletha–Prasad Axiom 4.1.20 on actual supplied integral models. It is a focused component of the full corrected Definition 4.1.26 interface; it asserts no model or building existence and gives no full-validity certificate.

## Source and scope

The source is Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), printed p.163, PDF p.194, Axiom 4.1.20(3)–(4), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The authors' 1 November 2024 corrections, PDF p.27, replace the Definition 4.1.26 list with the ten axiom groups and do not alter these two clauses. The corrections are registered as `kaletha-prasad-2024-corrections`, SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

The base `R` is an arbitrary local domain with fraction field `K`, both in universe `u`. These definitions apply to the valuation rings of the local fields in the full building task. They impose no characteristic restriction. A caller supplies the actual generic maximal split torus `S`, its map `i : S → G`, and the published `RelativeComponentModelData R K G`. The latter already supplies actual full and neutral smooth affine integral models, compatible generic identifications, connected neutral fibres and the all-test relative identity-component property. No model is constructed here.

## Source-to-declaration map

| Source | Declaration in `Langlands.BruhatTits.IntegralModels` | Meaning |
| --- | --- | --- |
| 4.1.20(3), generic fibre | `IntegralTorusData` | An actual commutative integral group scheme, a generic-fibre isomorphism to the supplied actual `S`, and an actual map to the neutral model, with the generic square commuting with `i`. |
| 4.1.20(3), closed integral split torus | `IntegralTorusData.IsClosedSplit` | `IsSplitTorus` over `Spec R` and `IsClosedSubgroup` of the actual inclusion. |
| 4.1.20(3), special fibre | `IntegralTorusData.specialFibre`, `specialFibreInclusion` | Actual base changes along the residue quotient `R → κ(R)`, with the commutative torus retained. |
| 4.1.20(3), maximal split special fibre | `IntegralTorusData.HasMaximalSplitSpecialFibre` | The published all-factorization `IsMaximalSplitTorus` predicate on the actual special-fibre inclusion. |
| Entire 4.1.20(3) on supplied data | `IntegralTorusData.SatisfiesTorusClause` | Conjunction of closed splitting and special-fibre maximality. |
| 4.1.20(4) | `RelativeComponentModelData.HasEqualComponentsForSimplyConnected` | If `G` is algebraically simply connected semisimple, the actual neutral-to-full inclusion is an isomorphism. |

The generic square is supplied data. The three torus predicates and the conditional equality-of-components predicate are expanded `Prop` definitions; they are not unconstrained labels. The torus maximality condition concerns `D.neutral.specialFibre` itself. No maximal reductive quotient is introduced or identified with that special fibre. The simply connected hypothesis uses the existing `IsSimplyConnected`, which includes `IsSemisimple` in its definition. The equality of models is expressed invariantly by their actual inclusion being an isomorphism, with its identity generic fibre already guaranteed by `RelativeComponentModelData`.

## Intrinsic law and remaining assembly

`IntegralTorusData.reduction_naturality` is the published base-change-section naturality theorem specialized to the actual torus inclusion and residue base map. It equates the two reductions of each integral torus section and introduces no geometric axiom.

The caller must quantify these supplied data and predicates over every nonempty bounded subset of every apartment of the actual building. The full/neutral integral-point equalities, facet and closure invariance, and the remaining special-fibre/facet clauses of Axiom 4.1.22 are separate assembly work of task `129deca1-ce21-411b-9b79-7e94545fe26d`. This focused unit does not identify fixers with generated parahorics, does not infer connected fibres from connected total space, and does not prove any structural axiom true.
