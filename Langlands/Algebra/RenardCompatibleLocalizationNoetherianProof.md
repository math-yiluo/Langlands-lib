# Noetherian unitized actions on actual endomorphism localization: proof

Author: Worker 735, for proof task `f7c49a61-e9b1-4576-8910-b846a70185d9`
under whole-book Renard task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`,
revision 2. The module is
`Langlands.Algebra.RenardCompatibleLocalizationNoetherianProof`, in
namespace `Langlands.Renard.AlgebraActionLocalization`. It imports the
published statement module
`Langlands.Algebra.RenardCompatibleLocalizationNoetherianStatements` by
name and does not change it or anything it imports.

The theorem `compatibleLocalizationNoetherian` has the complete closed type
`CompatibleLocalizationNoetherianStatements.{uB, uV}`. The algebra and
space universes stay independent. The theorem has no section parameters
and adds no premise.

## Provenance and scope

This is internal derived content motivated by David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, C.II, printed page 279 / PDF page 285. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 735 reread PDF page 285 for this proof. There, Renard proves that
the canonical map is surjective by writing `ã⁻¹` as a polynomial in `ã`
over `B`. He then obtains `K = ker aⁿ` from finite generation of the kernel
union `K`. No project errata file for this source exists in the Library
used here.

The Lean proof takes a different route. It applies the published
Noetherian localization core, whose surjectivity step is a quotient
Hopfian argument. Its kernel step stabilizes the ascending chain of power
kernels. Commutativity of `B` is not used. The algebra may be
noncommutative and nonunital. Its multiplication is complex-bilinear
through the two compatibility classes. The action `ρ` may be degenerate,
and the space `V` may be zero or of any complex dimension.

The proof covers exactly the three published internal targets. It does
not compare them with Renard's finite-type or Noetherian conventions. It
does not prove the complete source-facing C.II proposition or identify
the localization with the stable image. The compatible-power, criteria,
quotient, universal-property and unitization-finiteness branches are
untouched. All of these remain separate parent obligations.

## Data and local module selection

Throughout, `U = Unitization ℂ B`. For the actual data `ρ` and `f`, put
`a = f.toLinearMap` and use the actual `Localized a`, `iota a`,
`localizedEnd a`, `localizedInv a` and
`σ = localizedAction a ρ ha`. The source module structure on `V` is
exactly `CompatibleUnitization.module ρ`. On `Localized a` it is exactly
`CompatibleUnitization.module σ`. Both are selected locally, by `letI` in
helper types and by `let` inside proofs. No global instance is added.
The surjectivity helper's type selects only the localized action. Its
proof adds the source action internally to form the unitized maps, so the
first target has no hypothesis on `V`.

The proof uses three actual unitized maps, each obtained from a published
linear intertwiner by `CompatibleUnitization.ofLinearIntertwiner`. Each
has the same underlying function as its intertwiner.

- `A = ofLinearIntertwiner f : Module.End U V`, the unitized source
  endomorphism. This is the map whose powers define the target's
  `powers n`.
- `F = ofLinearIntertwiner (iotaIntertwiner a ρ ha) : V →ₗ[U] Localized a`,
  the unitized canonical map.
- `unitizedLocalizedEquiv a ρ ha`, a `U`-linear automorphism of
  `Localized a`, built with `LinearEquiv.ofLinearMap`. Its two maps come
  from `localizedEndIntertwiner` and `localizedInvIntertwiner`, and its
  inverse laws are the published identities `localizedEnd_localizedInv`
  and `localizedInv_localizedEnd`.

## Implemented proof

**Power coherence.** `unitizedLocalizedEquiv_pow_apply` shows that the
`n`-th power of the unitized automorphism, applied to `y`, equals
`(localizedEnd a ^ n) y`. `unitized_pow_apply` shows that
`(A ^ n) x = (a ^ n) x` for every `n` and `x`. Both proofs rewrite each
power as a function iterate with `LinearEquiv.pow_apply` or
`Module.End.pow_apply`, then close by definitional equality of the
underlying functions.

**Core certificates.** `unitized_intertwines_exhausts` proves the
intertwining identity `F (A x) = E (F x)` from the published
`iota_intertwines`. It also proves inverse-power exhaustion. Every element
of `Localized a` is an actual fraction `frac a x n` by `frac_surjective`.
By power coherence and `localizedEnd_pow_frac`, the `n`-th power of the
automorphism sends `frac a x n` to `iota a x = F x`.

**First target.** `surjective_of_isNoetherian` assumes only
`IsNoetherian U (Localized a)` for the σ-action. It applies the published
`NoetherianLocalizationCore.exhaustion_surjective` with ring `U`, source
`V`, target `Localized a`, and the maps `A`, the automorphism and `F`.
Surjectivity of `F` is surjectivity of the actual `iota a`, since the
functions coincide.

**Second target.** `stabilizationAt_of_isNoetherian` assumes Noetherianity
of both selected unitized modules. Local nilpotence of the kernel comes
from the published `iota_eq_zero_iff`: `iota a x = 0` gives some `m` with
`(a ^ m) x = 0`, hence `(A ^ m) x = 0` by power coherence. The published
`NoetherianLocalizationCore.localization_core` then returns surjectivity
of `F`. It also returns one exponent `n > 0` for which, as `U`-submodules,
`ker F = ker (A ^ n)`, `ker (A ^ n) = ker ((A ^ n) ^ 2)` and
`range (A ^ n) = range ((A ^ n) ^ 2)`. After unfolding
`CompatibleLocalizationStabilizationAt`, this same `n` is used for every
remaining conjunct.

- The compatible kernels `(iotaIntertwiner a ρ ha).ker` and
  `(powers n).ker` are equal by `CompatibleSubmodule.ext`. Membership in
  each is vanishing of `F` or of `A ^ n` respectively, because
  `toLinearIntertwiner (A ^ n)` has the underlying function of `A ^ n`.
- For `Stable (a ^ n)`, power coherence gives `(A ^ n) x = (a ^ n) x` and
  `((A ^ n) ^ 2) x = ((a ^ n) ^ 2) x`. The second follows by expanding
  both squares as composites. Rewriting membership in the complex kernels
  and ranges along these identities turns them into the `U`-linear
  kernel and range equalities.

So the strictly positive exponent identifying the compatible kernels is
the exponent at which the ordinary complex power `a ^ n` is stable.

**Third target.** `stabilizationAt_of_finite` assumes
`IsNoetherianRing U`, `Module.Finite U V` and
`Module.Finite U (Localized a)` for the selected actions. Mathlib's
`isNoetherian_of_isNoetherianRing_of_finite` holds over arbitrary unital
rings, so it gives both module Noetherian hypotheses. The proof then
applies the second target's helper.

**Aggregate.** `compatibleLocalizationNoetherian` introduces each target's
algebra, space, instances, `ρ` and `f`. It supplies the three helpers in
the published order. The first helper's compatibility proof argument is
unified with the statement's `fun b z => f.map_action' b z`.

## Verification

The module compiled on 29 October 2026 in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with no errors or warnings.
Inspection of `compatibleLocalizationNoetherian` reported a theorem with
level parameters `uB` and `uV`. It depends only on the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. It uses no `sorry`,
`admit` or new axioms. Development compilation is not acceptance.
Independent semantic review, the Lake build, exact-target validation and
Library publication are still required.
