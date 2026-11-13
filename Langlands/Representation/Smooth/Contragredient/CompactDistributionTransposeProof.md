# Renard III.1.6: compact-distribution transpose and compact fixed-dual restriction

Worker 338, Task 5961 (`e57418a0-4be3-4766-96de-c20d6ca8cfc3`).
Module
`Langlands.Representation.Smooth.Contragredient.CompactDistributionTransposeProof`,
namespace `Langlands`.

The theorem `contragredientDistributionLemma.{u,v}` proves exactly the published
`ContragredientDistributionLemmaStatement.{u,v}`. Its three component theorems
prove, respectively, `CompactDistributionContragredientTransposeStatement`,
`CompactSubgroupHaarTransposeStatement` and `CompactFixedDualRestrictionStatement`.
The group and representation carrier have independent universes `u,v`.
The existing statement and its imported files are unchanged.

## Source and scope

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source result is III.1.6, Lemma, printed p.61 / PDF p.67. Its scalar
distribution action is defined in III.1.3, printed p.59 / PDF p.65. These source
pages were read for this proof.

The first two component statements quantify distribution actions satisfying
the published scalar pairing characterization. The proof applies that
characterization without constructing or assuming an additional action.
The third component has no distribution-action premise and is proved independently.
Every compact subgroup is allowed, including non-open ones. There is no
finite-dimensionality or admissibility hypothesis and no choice of ambient Haar
measure.

## Compact distribution transpose

`compactDistributionContragredientTranspose` fixes a smooth functional `ℓ`
and a vector `x`. Smoothness of `x` makes the coefficient
`φ(g) = ℓ(ρ(g)x)` locally constant, using `Hecke.orbitMap_locallyConstant`.
Evaluation at `x` is a linear functional `ev` on `SmoothDual ρ`. Applying the
contragredient action's characterization with `ev` and `invFunction φ`
computes the left side as the pairing of `Tinv` with `g ↦ φ(g⁻¹)`.

The assumed equality of underlying distributions identifies `Tinv` with
`Distribution.RenardHecke.compactInversion T` by subtype extensionality.
The published `compactSupportPairing_compactInversion` transfers inversion
to the coefficient. Double inversion returns `φ`, and the characterization
of the original action gives `ℓ(act T x)`. This implements the source's
pushforward computation directly.

## Compact subgroup Haar

`compactSubgroupHaarTranspose` obtains the transpose formula by applying the
preceding theorem to `e_K` twice. The required inversion equality is the
published `inversionDistributions_compactSubgroupHaar`, which applies to
arbitrary compact subgroups.

The private helper `compactHaar_pairing` computes the extended pairing of
`e_K` with a locally constant `φ` as its scalar integral on `K` against
`Measure.haarMeasure ⊤`. To prove it, choose an ambient test agreeing with `φ`
on the compact set `K`. The support of `e_K` is contained in `K`, so
`compactSupportFunctional_eq_of_agrees` computes the extended pairing by that
test. The defining Haar formula and pointwise equality on `K` give the integral.
This is a derived compatibility lemma for the existing distribution definitions.

For a `K`-invariant algebraic linear form `m`, the coefficient
`g ↦ m(ρ(g)x)` equals `m(x)` on `K`. The scalar action characterization and
the helper reduce its value on `act(e_K)x` to the integral of this constant.
The published `isProbabilityMeasure_haarMeasure_top` normalizes the subgroup
measure, giving exactly `m(x)`.

## Full fixed-dual restriction

`compactFixedDualRestriction` restricts `ρ` to the actual group `K`, denoting
this representation by `τ`. The locally constant orbit map restricted along
the continuous subgroup inclusion has finite range, since `K` is compact.
Thus `Compact.CharZero.orbit τ x` is finite for every `x`, with no topology
on the representation carrier.

Define `A(x) = Compact.CharZero.orbitMean τ x`, the normalized sum of the
distinct orbit vectors. The published `orbitMean_add` and `orbitMean_smul`
make `A` linear. The published `orbitMean_invariant` places its image in
`fixedVectors ρ K`, defining a linear map `P : V → V^K`.
The laws `orbitMean_id` and `orbitMean_apply` give
`P(x) = x` for fixed vectors and `P(ρ(k)x) = P(x)` for `k ∈ K`.

The private helper `dual_orbitMean_of_constant` shows that an algebraic linear
form constant on an orbit takes its original value on that orbit's normalized
mean. It expands the finite sum, moves the linear form through it, and cancels
the nonzero orbit cardinality in `ℂ`. A form fixed by `ρ.dual` has this
constancy property: evaluate its fixedness at `k⁻¹` to obtain
`m(ρ(k)x) = m(x)`. Hence every invariant form satisfies `m(P(x)) = m(x)`.

If two invariant forms restrict equally to `V^K`, evaluate that equality at
`P(x)` to prove equality on every `x`; this proves injectivity. For
`μ : (V^K)*`, the form `μ.comp P` is `K`-invariant by
`P(ρ(k⁻¹)x) = P(x)` and restricts to `μ` because `P` fixes `V^K`.
This proves surjectivity for the full algebraic dual. The extension is not
required to be a smooth functional.

The finite orbit construction is the implementation of the projector argument
cited at the end of Renard's III.1.6 proof; its finite-mean laws are reused from
the published `Compact.CharZeroAverage` module. The aggregate theorem packages
the three component proofs.

## Validation

The module compiled with no errors or warnings under the task's environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`. Declaration inspection reported both
universe parameters and only `propext`, `Classical.choice` and `Quot.sound`.
Independent semantic review and the submission's exact-target validation
remain separate requirements.
