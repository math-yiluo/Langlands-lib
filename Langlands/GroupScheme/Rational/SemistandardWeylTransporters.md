# Literal semistandard Levi Weyl transporters and finite sums

This module constructs Weyl transporter carriers from literal subgroup functors,
their left target-Weyl quotients, and elementary finite sums. It also states
three geometric comparison targets needed to use these carriers with the full
semistandard spectral family. The spectral action, normalized operators,
wave-packet Fourier identities and packet pairing identities are subsequent
constructions and targets.

All declaration names below belong to `Langlands.GroupScheme`.

## Original source and formalization scope

The registered original is J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003),
235–333, DOI 10.1017/S1474748003000082, source
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
V.1, printed p.288 / PDF p.54, defines

```
𝒲(M'|G|M) = {s ∈ W^G | s·M ⊆ M'},
W(M'|G|M) = W^M' \ 𝒲(M'|G|M).
```

The source allows empty carriers and chooses representative systems for the
quotient. VII.2.1 and VII.2.2, printed pp.317–318 / PDF pp.83–84, use Weyl sums
for the same Levi and for conjugate Levis, respectively. VII.2.3, printed
p.319 / PDF p.85, treats nonconjugate Levis. The present finite sums supply the
algebraic indexing prerequisite of those formulas.

The inclusion carrier directly follows V.1. The separate equality carrier is
a derived interface for the conjugate-Levi case. Equality of the two carriers
for rationally conjugate Levis is an explicit unproved target here; it is not
silently substituted for the source's inclusion condition.

The construction works over an arbitrary field `k : Type u`, with a group
scheme `G` and a commutative group scheme `T` over `Spec k`, and a morphism
`i : T.toGrp ⟶ G`. The carrier definitions do not require a local-field topology,
splitness, affine hypotheses or reductivity. Actual connected reductivity and
maximal splitness enter the finiteness theorem and the three comparison targets.
Finiteness of this algebraic Weyl index makes no assertion about Fourier support.
The finite-sum codomain `A : Type v` has an independent universe and only an
`AddCommMonoid` structure.

## Actual subgroup and quotient constructions

`SemistandardSpectralLevi i`, imported from `SemistandardSpectralIndex`, consists
of the literal all-test Levi subgroup functors occurring in intrinsic
semistandard indices. A Levi is not replaced by an isomorphic chosen group.
The ambient group is the published `relativeWeylGroup i`, the actual quotient
`normalizerPoints i / centralizerPoints i`.

`semistandardLeviRelativeWeylSubgroup i M` defines `W^M` as the image in that
quotient of the normalizer points lying in `M.val.rationalPoints`.
`mem_semistandardLeviRelativeWeylSubgroup` gives its existential lift formula.
When `hM : torusCentralizer i ≤ M.val` is supplied,
`mk_mem_semistandardLeviRelativeWeylSubgroup_iff` proves that membership of any
normalizer lift in this Weyl subgroup is equivalent to membership of that very
lift in the literal Levi.

`semistandardWeylTransporterSet i M M' hM` imposes
`relativeWeylConjugateSubgroupFunctor i M.val hM w ≤ M'.val`.
`semistandardWeylConjugacySet` imposes equality instead.
The imported `relativeWeylConjugateSubgroupFunctor` already proves independence
of the normalizer lift under the explicit source containment `hM`. For a lift
`n`, it is exactly
`M.val.comap (G.innerIso n).inv`, the image `n M n⁻¹` on every test scheme.
The two `mk_mem_..._iff` lemmas expose these literal representative formulas.
`semistandardWeylConjugacySet_subset_transporter` proves the immediate inclusion.

`mul_mem_semistandardWeylTransporterSet` and
`mul_mem_semistandardWeylConjugacySet` prove stability under left multiplication
by `W^M'`. Their hypotheses require membership in the actual target Weyl
subgroup; no target centralizer-containment assertion is needed for this step.

`semistandardWeylTransporterRel` and `semistandardWeylConjugacyRel` restrict
Mathlib's `QuotientGroup.rightRel W^M'` to the corresponding carrier.
Consequently both quotient types,
`SemistandardWeylTransporterQuotient` and
`SemistandardWeylConjugacyQuotient`, are **left** target-Weyl quotients:

```
[s] = [t]  ↔  t * s⁻¹ ∈ W^M'.
```

`semistandardWeylConjugacyQuotient_mk_eq_iff` proves this formula, and
`semistandardWeylConjugacyQuotient_mk_surjective` supplies representatives.
The quotient is formed at the Weyl transporter level. Distinct quotient classes
that act identically on a later orbit are retained, so no orbit-image quotient
removes Weyl multiplicities or stabilizer contributions.

Both quotients have `Finite` instances when the ambient Weyl group is finite.
`finite_semistandardWeylQuotients` supplies this conclusion from
`IsConnectedReductive G` and `IsMaximalSplitTorus i`. It obtains a generic
cocharacter from the published split-torus existence theorem and applies the
published `relativeWeylCoxeter` theorem. No generic cocharacter is required as
additional input to this finiteness theorem.

## Summands, sums and proved identities

`semistandardWeylConjugacyDescend` descends a function on the equality
transporter to its actual quotient only when supplied with the exact law
`t*s⁻¹ ∈ W^M' → term s = term t`.
`semistandardWeylConjugacyDescend_mk` proves its representative evaluation.
This is an elementary descent utility; it does not supply or assume a
spectral comparison operator.

`semistandardWeylConjugacySum` is the finite sum over the equality-transporter
quotient, using `Fintype.ofFinite`. Its zero and congruence lemmas are proved.
`semistandardWeylConjugacySum_descend` expresses a descended sum using
`Quotient.out` representatives. Combined with the descent evaluation, the same
term can be evaluated using any representative of each quotient class.

`isRationallyConjugate_of_mem_semistandardWeylConjugacySet` extracts an actual
normalizer lift and proves `M.val.IsRationallyConjugate M'.val`. This is the
published rational-conjugacy predicate on all test schemes, with witness in
`G(k)`. Therefore `isEmpty_semistandardWeylConjugacyQuotient` proves emptiness
for nonconjugate literal Levis, and
`semistandardWeylConjugacySum_of_not_conjugate` proves that every such sum is
zero. There is no claim that every empty equality transporter has nonconjugate
Levis without the coverage target below.

## Exact remaining targets and dependency map

| Declaration | Precise conclusion and status |
| --- | --- |
| `SemistandardLeviCentralizerContainmentStatement` | For arbitrary fields, connected reductive `G` and maximal split `i`, every intrinsic semistandard Levi contains the full `torusCentralizer i` on all test schemes. This is a Prop-valued target. |
| `semistandardLeviCentralizerContainment_of_dynamicCoverage` | Proved conditional implication from the published `SemistandardSpectralDynamicCoverageStatement` to the preceding target. Dynamic coverage itself is not asserted here. |
| `SemistandardWeylConjugacyCoverageStatement` | Under the same geometric hypotheses, for any `M,M'` and explicit source containment `hM`, rational conjugacy of their literal Levi functors implies a nonempty equality-transporter quotient. This is a Prop-valued target. |
| `SemistandardWeylTransporterEqualityStatement` | Under the same hypotheses, for any `M,M'` and explicit `hM`, rational conjugacy implies equality of the inclusion and equality transporter sets. This is a Prop-valued target. |

The conditional containment proof presents `M` by an intrinsic index, applies
dynamic coverage to that index, compares the Levi fields, and uses
`torusCentralizer_le_dynamicCentralizer`. The three target statements record
geometric obligations of this interface; neither their proofs nor the full
semistandard coverage and uniqueness proofs are supplied by this file.

The other elementary proofs use the following published inputs:

- `StandardLeviLiftIndependence` supplies the all-test, lift-independent Weyl
  action and `SubgroupFunctor.comap_innerIso_hom_eq_of_mem`. For left stability,
  choose lifts of the two Weyl factors, rewrite conjugation of their product
  using `innerIso_mul_hom` and `comap_comp`, and use that a point of `M'`
  preserves `M'` under inner conjugation.
- `ParabolicConjugacyTransport` supplies the exact rational-conjugacy predicate
  and `SubgroupFunctor.eq_comap_iso_iff`; these convert an equality-transporter
  representative into the claimed conjugacy witness.
- `RelativeWeylCoxeterProof` supplies actual ambient Weyl finiteness under
  reductivity and maximal splitness. Mathlib supplies quotient finiteness,
  quotient descent and finite-sum laws.

The subgroup membership proof compares lifts by `m⁻¹*n` in the actual
centralizer, applies `hM` at the base test scheme, and uses subgroup
multiplication. Quotient descent is `Quotient.lift` with the exact relation
law. The representative sum identity uses `Quotient.out_eq` and finite-sum
congruence. Empty-quotient and zero-sum proofs use the actual rational-conjugacy
witness just described.

This is a derived algebraic prerequisite of the Waldspurger VII.2.1–VII.2.3
wave-packet Fourier and pairing targets. It reuses the published intrinsic
indices of `SemistandardSpectralIndex`; full spectral families and smooth
coherent sections, and the construction and descent laws of the particular
normalized comparisons and rational-point translations, are not part of this
file. The present file constructs none of those operators. Source packets,
density and orbit measure, and the full Fourier family, are not part of this
file either. In particular, the finite-sum utility here is not
the substantive VII.2.1 or VII.2.2 spectral formula; those subsequent targets
must supply the actual spectral summands and representative transports.
