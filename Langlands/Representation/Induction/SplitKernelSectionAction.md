# Section actions on localized kernel quotients

This is an internal elementary construction from the published character-localization,
ordinary coinvariant and twist definitions. It works over an arbitrary commutative
ring `R`, with independent universes for `G`, `L`, `V`, `W`, and `X`. The complex
split-retraction specialization is supplied separately, in `SplitKernelLocalizationData`. The present algebra does
not require a retraction law: normality of `r.ker` is sufficient.

The namespace is `Langlands.Induction.SplitKernelLocalization`.
`inverseSectionConjugate r s l n` is the actual element `(s l)⁻¹ * n * s l`
of `r.ker`. The hypothesis is exactly invariance under this inverse conjugation.

| Construction or law | Implemented proof and exact scope |
| --- | --- |
| `sectionRelationsStable` | On a generator, apply the relation at `inverseSectionConjugate r s l⁻¹ n` and `rho (s l) v`. The homomorphism law for `s` and character invariance simplify this to the image of the original generator; span induction gives stability. |
| `sectionAction`, `sectionAction_mk`, `sectionQuotientMap` | `Representation.quotient (rho.comp s)` supplies the actual representation and proves its identity/multiplication laws. Its module is definitionally `Jacquet.Localization.Coinvariants rho r.ker theta`. The class law is `l [v] = [rho (s l) v]` and the quotient map is the canonical `mk`. |
| `sectionMap`, `sectionMap_mk`, `sectionMap_id`, `sectionMap_comp` | The underlying linear map is the published `Localization.mapLinear`. Equivariance follows from the original intertwiner on representatives. Surjectivity of `mk` proves identity and composition. Intertwiners between different carrier universes are allowed. |
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
`def` or citation supplies no proof.

| Exclusion condition | Direct and transitive dependency check |
| --- | --- |
| `SupercuspidalCoinvariantFinitenessStatement` (all-character single-block), every module proving it and every downstream consequence | Absent from the entire closure; no finite-dimensionality or finiteness input occurs. Missing general derivative or tensor inputs are not assumed from consumers. |
| `GenericSegmentProductUniqueness` | Absent from the closure and from all proof terms; no genericity or uniqueness result is used. |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible` | Neither these consumers nor the modules proving them or their consequences occur. The elementary quotient construction has no segment input. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom` and the modules that prove them | Absent throughout the closure; no socle product or quotient comparison is used. |
| `SegmentSocleProductIrreducibility` | Absent, including the modules that prove it and downstream consequences. |
| `AdjacentUnlinkedSegmentSocleSwap`; `TwoSegmentSocleCommutation` | No adjacent swap or segment commutation result is imported or invoked, directly or transitively. |
| `LinkedSegmentSocleGluing` | Absent throughout; no gluing statement is used. |
| `OrderedMultisegmentSocleExistence`; socle exhaustion | No existence or exhaustion theorem enters the construction. |
| Individual special-head/reverse-socle existence; individual segment-socle/reverse-head existence | Both families, the modules that prove them, and their consequences are absent. |
| Segment analytic classification; forward `SegmentSpecialEssentialSquareIntegrability` | No analytic, classification or square-integrability result appears anywhere in the closure. |
| Multisegment/special-head exhaustion; ordered strong/special-head existence; quotient coverage; ordered conversion | All four families, the modules that prove them and all of their downstream consequences are absent, directly and transitively. |
| Tempered/block uniqueness; `SquareIntegrableLanglandsClassification`; square-integrable exhaustion; regular exhaustion | No tempered, square-integrable, regular or classification input enters any dependency. |
| `SegmentHeadProductIrreducibility` | The special-head criterion, all of its conclusions, the modules that prove it and its transitive dependents are absent. |
| Every segment derivative formula, segment-socle/head existence or Jacquet formula, segment classification, and clauses (b), (d), (e), (f) of the six statements of `Classification.SegmentSocleDerivativesStatement` | None is imported, assumed, or used to prove a lower input. No general derivative theorem or clause (a)/(c) is used either; no unproved proposition is treated as proved. |
| `TwoSupercuspidalNonadjacentProductIrreducible`; `TwoSupercuspidalProductStructure` (full-product assembly) | No two-supercuspidal product result, module proving one, or downstream consequence enters the closure. |
| `SegmentFullJacquetFormula` and its proof `segmentFullJacquetFormula` (`Classification.SegmentFullJacquetProof`); `SegmentHeadJacquetFormula`; `SegmentSocleJacquetFormula`; `SegmentSpecialJacquetExponentNormFormula` | All four formula families and their mathematical consequences are absent. The generic algebraic module named `Jacquet.Coinvariants` contains only actual relation quotients and elementary maps, not any of these formulas. |
| Ze80 §§3.5, 9.6 derivative formulas; Ze80 4.2/9.7 irreducibility; Ze80 9.3 analytic/square-integrability; classification/exhaustion; the circular route from Ze80 4.2 through §2 to Proposition 1.11 | None is cited or used as proof evidence. No unproved BZ77 derivative assertion is assumed. |
| `IrreducibleCoinvariantFinitenessStatement`; `LeviCuspidalCoinvariantFinitenessStatement`; mirabolic finite-length route | These finiteness conclusions, the modules that prove them and downstream consequences are absent. No finite-length repair is used. |
| Shared lower derivative functors, exactness, Leibniz/support filtrations, geometric lemma, cuspidal support, tensor results, finite length, plus-functor theorems | None is a proof input. Only the explicitly listed elementary representation modules are used; no matrix `plusSubgroup` result or consumer comparison is involved. |
| Compact induction, relative integration, Haar section covariance, induction in stages, support filtrations, exactness, all six mixed-minus comparison clauses | No such theorem is proved or assumed here. No Haar character, determinant, modulus, or half-density factor enters the section action. Ordinary quotient maps/equivalences are constructed from relation spans. |

Arbitrary zero modules and independent carrier universes remain allowed. No
admissibility, irreducibility, finite dimension/length, unitarity, nonzero vector,
coefficient topology, or triviality of a restricted character is assumed. The
smoothness argument uses open stabilizers and continuous group restriction only.
