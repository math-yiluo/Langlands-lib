# Section actions on localized kernel quotients

This is an internal elementary construction from the published character-localization,
ordinary coinvariant and twist definitions. It works over an arbitrary commutative
ring `R`, with independent universes for `G`, `L`, `V`, `W`, and `X`. The complex
split-retraction specialization is supplied separately. The present algebra does
not require a retraction law: normality of `r.ker` is sufficient.

The namespace is `Langlands.Induction.SplitKernelLocalization`.
`inverseSectionConjugate r s l n` is the actual element `(s l)⁻¹ * n * s l`
of `r.ker`. The hypothesis is exactly invariance under this inverse conjugation.

| Construction or law | Implemented proof and exact scope |
| --- | --- |
| `sectionRelationsStable` | On a generator, apply the relation at `inverseSectionConjugate r s l⁻¹ n` and `rho (s l) v`. The homomorphism law for `s` and character invariance simplify this to the image of the original generator; span induction gives stability. |
| `sectionAction`, `sectionAction_mk`, `sectionQuotientMap` | `Representation.quotient (rho.comp s)` supplies the actual representation and proves its identity/multiplication laws. Its module is definitionally `Jacquet.Localization.Coinvariants rho r.ker theta`. The class law is `l [v] = [rho (s l) v]` and the quotient map is the canonical `mk`. |
| `sectionMap`, `sectionMap_mk`, `sectionMap_id`, `sectionMap_comp` | The underlying linear map is the accepted `Localization.mapLinear`. Equivariance follows from the original intertwiner on representatives. Surjectivity of `mk` proves identity and composition. Intertwiners between different carrier universes are allowed. |
| `isSmooth_sectionAction` | Continuous restriction along `s`, followed by the actual surjective equivariant quotient map, preserves smoothness. No topology on `R` or the representation carrier is introduced. |
| `ordinarySectionRelationsStable`, `ordinarySectionAction`, `ordinarySectionAction_mk`, `ordinarySectionMap`, `ordinarySectionMap_mk` | The same conjugation calculation with ordinary relations constructs the ordinary kernel quotient action induced along `s`, and its actual class map on any intertwiner. |
| `relations_eq_twisted` | If `chi` restricts to `theta` on `r.ker`, multiplying a generator of the ordinary relations for `twist chi⁻¹ rho` by the unit `theta n` gives the character relation. Multiplying a character relation by its inverse gives the reverse inclusion. This proves equality of submodules over arbitrary `R`. |
| `twistSectionEquiv`, `twistSectionEquiv_mk`, `twistSectionEquiv_natural` | `Submodule.quotEquivOfEq` gives the identity on classes. If `chi (s l) = 1`, the twisted section operator equals the original section operator, so this is an equivalence of the actual `L` representations. Naturality is equality on all quotient representatives, with the ordinary map applied to `twistIntertwining chi⁻¹ f`. |

The action is **unnormalized**: it has no scalar factor. BZ77 §1.8,
printed pp.444–445 (one-based PDF pp.5–6), uses the character relation
`rho(u)v - theta(u)v` and additionally discusses a modulus normalization. That
normalization is deliberately absent from this construction. BZ77 §7.2,
printed p.471 (PDF p.32), motivates its eventual single-orbit use; it is not
a proof premise here. These pages were read in text and as rendered page images.
No source-specific project erratum was found in the available errata/notes
locations. Source: `bernstein-zelevinsky-1977-induced-i`, Bernstein–Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977), retained PDF
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
All new proofs follow the explicit elementary route described above, not a
compact-induction comparison from that paper.

The only direct project import is
`Langlands.Representation.Jacquet.LocalizationTransport`.
The complete transitive project import closure, excluding this entry, is:

- `Langlands.Representation.Jacquet.Coinvariants`
- `Langlands.Representation.Smooth.Definitions`
- `Langlands.Representation.Smooth.Transfer.PullbackStatement`
- `Langlands.Representation.Smooth.Transfer.PullbackProof`
- `Langlands.Representation.Smooth.Transfer.SubquotientStatement`
- `Langlands.Representation.Smooth.Transfer.SubquotientProof`
- `Langlands.Representation.Twist.Definitions`
- `Langlands.Representation.Twist.SmoothStatement`
- `Langlands.Representation.Twist.SmoothProof`
- `Langlands.Representation.Jacquet.SmoothTwist`
- `Langlands.Representation.Category.Basic`
- `Langlands.Representation.Jacquet.Localization`
- `Langlands.Representation.Jacquet.LocalizationTransport`

The full project closure above has been inspected, including the implementations
behind the smooth-transfer statements. Its mathematics consists only of group
homomorphisms, linear representations, scalar twists, open stabilizers,
submodule spans and quotients, and elementary categorical packaging. No imported
module contains a segment, parabolic, derivative, Whittaker-finiteness or
classification conclusion. The following checks apply to every new construction
and proof and to all of its direct and transitive proof inputs. A statement
`def`, citation, draft, pending proof, or peer ownership message supplies no proof.

| Inherited exclusion condition | Direct and transitive dependency check |
| --- | --- |
| `SupercuspidalCoinvariantFinitenessStatement`, all-character single-block task `62de5903-b616-4b5c-88eb-a066b77c5467`, and every successor/downstream consequence | Absent from the entire closure; no finite-dimensionality or finiteness input occurs. Missing general derivative or tensor inputs are not assumed from consumers. |
| `GenericSegmentProductUniqueness`, task `30341ae4-65f2-4a0e-9283-763db01a409e` | Absent from the closure and from all proof terms; no genericity or uniqueness result is used. |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`; tasks `23e98d90-6055-4e35-91a9-b0f5d8a84961`, `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`, `8fa9f68b-fa1b-431a-97f6-5b163964d1fc` | Neither these consumers nor their successors or consequences occur. The elementary quotient construction has no segment input. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom`, task `7ff2a1e9-89dc-439e-a861-a567b3db92bf` and proof successors | Absent throughout the closure; no socle product or quotient comparison is used. |
| `SegmentSocleProductIrreducibility`, task `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | Absent, including successors and downstream consequences. |
| `AdjacentUnlinkedSegmentSocleSwap`, tasks `e3634665-571b-4852-9f4c-bab8a1053434`, `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`; `TwoSegmentSocleCommutation`, tasks `426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0` | No adjacent swap or segment commutation result is imported or invoked, directly or transitively. |
| `LinkedSegmentSocleGluing`, tasks `c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea` | Absent throughout; no gluing statement is used. |
| `OrderedMultisegmentSocleExistence`, task `23189526-80b0-4828-a6d4-7ebec2cbeef5`; socle exhaustion `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | No existence or exhaustion theorem enters the construction. |
| Individual special-head/reverse-socle existence `67279e36-f3c2-42e3-9302-11729784042e`; individual segment-socle/reverse-head existence `4ca79bbd-589e-476b-9f65-661e799984b5` | Both families, their successors, and their consequences are absent. |
| Segment analytic classification `aca8805b-054f-4d56-8045-12db7f623404`; forward `SegmentSpecialEssentialSquareIntegrability`, task `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | No analytic, classification or square-integrability result appears anywhere in the closure. |
| Multisegment/special-head exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`; ordered strong/special-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`; quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`; ordered conversion `8252833d-c269-41a9-824c-5879e531b23b` | All four families and all of their successors/downstream consequences are absent, directly and transitively. |
| Tempered/block uniqueness `52e97845-36bb-457d-b76f-70753334b88c`; `SquareIntegrableLanglandsClassification`, task `1cb45da2-7007-4351-a694-594fb148b8d1`; square-integrable exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4`; regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac` | No tempered, square-integrable, regular or classification input enters any dependency. |
| `SegmentHeadProductIrreducibility`, task `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | The special-head criterion and all of its conclusions/successors/transitive dependents are absent. |
| Every segment derivative formula, segment-socle/head existence or Jacquet formula, segment classification, and clauses (b), (d), (e), (f) of the parent six-statement contribution | None is imported, assumed, or used to prove a lower input. No general derivative theorem or clause (a)/(c) is used either; no pending proposition is treated as proved. |
| `TwoSupercuspidalNonadjacentProductIrreducible`, task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`; `TwoSupercuspidalProductStructure`, full-product assembly `ab61f565-1427-4746-ba77-46097563e962` | No two-supercuspidal product result, successor, or downstream consequence enters the closure. |
| `SegmentFullJacquetFormula`, arrangement `ed48ae06-964c-4c84-9e62-978f5a953ca7` and exact proof successor; `SegmentHeadJacquetFormula`, task `55ad1e10-62d8-46b7-a081-909ef0056426`; `SegmentSocleJacquetFormula`, task `b95105c6-f8bb-4641-ae53-2f49d1e7f034`; `SegmentSpecialJacquetExponentNormFormula`, task `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | All four formula families and their mathematical consequences are absent. The generic algebraic module named `Jacquet.Coinvariants` contains only actual relation quotients and elementary maps, not any of these formulas. |
| Ze80 §§3.5, 9.6 derivative formulas; Ze80 4.2/9.7 irreducibility; Ze80 9.3 analytic/square-integrability; classification/exhaustion; the circular route from Ze80 4.2 through §2 to Proposition 1.11 | None is cited or used as proof evidence. No unproved BZ77 derivative assertion is assumed. |
| `IrreducibleCoinvariantFinitenessStatement`, task `5ab445dc-d2b4-4072-80d1-6370870a4a26`; `LeviCuspidalCoinvariantFinitenessStatement`, task `3ff5c8fb-397c-4345-bcb3-5d98a0993d18`; mirabolic finite-length route `5428fe2c-013c-482d-aa6e-7df43e7191aa` | These finiteness conclusions, proof successors and downstream consequences are absent. No finite-length repair, pending or otherwise, is used. |
| Shared lower derivative functors, exactness, Leibniz/support filtrations, geometric lemma, cuspidal support, tensor results, finite length, plus-functor theorems | None is a proof input. Only the explicitly listed elementary representation modules are used; no matrix `plusSubgroup` result or consumer comparison is involved. |
| Compact induction, relative integration, Haar section covariance, induction in stages, support filtrations, exactness, all six mixed-minus comparison clauses | No such theorem is proved or assumed here. No Haar character, determinant, modulus, or half-density factor enters the section action. Ordinary quotient maps/equivalences are constructed from relation spans. |

Arbitrary zero modules and independent carrier universes remain allowed. No
admissibility, irreducibility, finite dimension/length, unitarity, nonzero vector,
coefficient topology, or triviality of a restricted character is assumed. The
smoothness argument uses open stabilizers and continuous group restriction only.
Worker 127's operator pause and every current operator suspension are preserved;
no paused worker is contacted or awakened. Coordination ownership is not a
mathematical premise. The later comparison statement/proof remains with its
existing owners, in dependency order.
