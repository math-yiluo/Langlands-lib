# Compatible morphisms of supplied Bruhat–Tits models

This focused definition unit expresses the preamble and part (1) of Kaletha–Prasad Axiom 4.1.22 on actual supplied full and neutral integral models. The data, the special fibres, the restriction square and the kernel are actual group schemes and morphisms. It supplies no models, no comparison map existence and no full corrected building certificate.

## Source and scope

The source is Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), printed p.163, PDF p.194, Axiom 4.1.22 up to and including (1), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The authors' 1 November 2024 corrections, PDF p.27, include 4.1.22 in the corrected ten-item Definition 4.1.26 list and do not change these clauses. The corrections are registered as `kaletha-prasad-2024-corrections`, SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

The integral base is an arbitrary domain `R` with fraction field `K`, in arbitrary universe `u`; the residue section requires `R` to be local. No characteristic restriction is imposed. The actual valuation rings in the surrounding KP task specialize these definitions. Both models have generic fibre identified with the same actual group `G`. The published `RelativeComponentModelData` already supplies smooth affine full and neutral models, connected neutral fibres and the all-test relative identity-component assertion. This file does not infer connected fibres from connected total space.

## Source-to-declaration map

All declaration names below are in `Langlands.BruhatTits.IntegralModels`.

| Source | Declaration | Meaning |
| --- | --- | --- |
| 4.1.22, first paragraph | `RelativeComponentModelHom.full` | The actual full-model morphism, with the identity generic-fibre square provided by `IntegralModel.Hom`. For `Ω ≺ Ω'`, `source` denotes the model of `Ω'` and `target` denotes the model of `Ω`. |
| 4.1.22, restriction to identity components | `RelativeComponentModelHom.neutral`, `component_comm` | A compatible actual neutral-model morphism and its commuting square with the two relative-component inclusions. |
| 4.1.22, induced residue morphisms | `fullSpecialFibreMap`, `neutralSpecialFibreMap`, `specialFibre_component_comm` | Actual base change of the two maps along `R → κ(R)`, retaining the commuting restriction square. The source's barred `ρ` is `neutralSpecialFibreMap`. |
| 4.1.22, isomorphism on every torus | `PreservesTori` | For every torus `T` and closed inclusion `i` into the source neutral special fibre, the actual composite `i ≫ neutralSpecialFibreMap` is a closed immersion into the target neutral special fibre. |
| 4.1.22(1), kernel | `specialFibreKernel`, `HasSmoothConnectedUnipotentKernel` | The actual group-scheme kernel constructed as the pullback with the unit, with smoothness, Zariski connectedness and unipotence over `κ(R)` required explicitly. |
| 4.1.22, preamble's special-fibre assertion and (1) | `SatisfiesGeneralSpecialFibreClauses` | Conjunction of the preceding two expanded predicates, for subsequent indexing over all ordered nonempty bounded subsets. |

The model morphisms and their compatibility are supplied data. `PreservesTori` and `HasSmoothConnectedUnipotentKernel` are validity assertions, each expanded as a `Prop` formula. The torus predicate uses the published `IsTorus`, so its universal quantifier includes nonsplit tori. Asking that the composite be a closed immersion expresses the isomorphism onto a torus invariantly: its domain `T`, with this new inclusion, is the actual image torus and the restriction is the identity isomorphism onto that realization. This constrains the specified map on every torus; it is stronger than saying that its rational-point image is a torus or that an unrelated torus is isomorphic to `T`.

The kernel uses `Langlands.GroupScheme.kernel`, whose actual pullback construction and pointwise kernel equivalence are already public. The kernel is a subgroup of the neutral special fibre; neither that special fibre nor its kernel is replaced by a maximal reductive quotient. No unipotent-radical quotient theorem or perfect-field reductivity theorem is assumed here.

## Intrinsic laws and remaining assembly

`full_integralPointMap` and `neutral_integralPointMap` specialize the published integral-point naturality theorem to the identity of `G`. They show that the two maps act as the identity on their generic-point images. `full_integralPoints_le` and `neutral_integralPoints_le` then give actual subgroup inclusions inside `G(K)`. Thus, after the surrounding validity predicate identifies these images with the required fixers, these model maps recover the stated fixer inclusions without an additional arbitrary point-map choice. No injectivity or surjectivity of reduction is asserted.

`specialFibre_component_comm` applies the base-change functor to `component_comm`. `full_reduction_naturality` and `neutral_reduction_naturality` specialize the existing residue-section naturality laws. These are intrinsic consequences of the supplied maps and prove none of the structural special-fibre predicates.

The caller must index these data over every ordered pair of nonempty bounded apartment subsets in the source relation `Ω ≺ Ω'`. The actual ordering, the full and neutral integral-point/fixer equalities from 4.1.20, all facet-only parts 4.1.22(2)–(7), and the full corrected ten-axiom assembly remain obligations of task `129deca1-ce21-411b-9b79-7e94545fe26d`. This focused unit does not claim any of them.
