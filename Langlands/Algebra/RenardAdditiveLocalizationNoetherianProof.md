# Noetherian actual localization of additive nonunital actions: proof

Author: Worker 735, for proof task `4dc9ca3f-973e-4bad-a62f-882725858442`
under whole-book Renard task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`,
revision 2. The module is
`Langlands.Algebra.RenardAdditiveLocalizationNoetherianProof`, in
namespace `Langlands.Renard.AdditiveActionLocalization`. It imports the
published statement module
`Langlands.Algebra.RenardAdditiveLocalizationNoetherianStatements`, the
published kernel lemma module
`Langlands.Algebra.RenardEndomorphismLocalizationKernelProof` and the
published core proof module
`Langlands.LinearAlgebra.NoetherianLocalizationCoreProof` by name. It
changes none of them, nor anything they import.

The theorem `additiveLocalizationNoetherian` has the complete closed type
`AdditiveLocalizationNoetherianStatements.{uA, uV}`. The acting-ring and
carrier universes stay independent. The theorem has no section
parameters and adds no premise.

## Provenance and scope

This is internal derived content motivated by David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, C.II, printed page 279 / PDF page 285. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 735 rechecked this hash and reread PDF page 285 for this proof.
There, Renard first writes `ã⁻¹` as a polynomial in `ã` over the
commutative algebra `B`. So `ι(L)` is stable under `ã⁻¹`, and the
universal problem gives surjectivity of `ι`. He then shows that the
kernel union `K` is finitely generated, so `K = ker aⁿ` for some nonzero
`n`. On 30 October 2026, the Renard notes in Library commit `ea472686`
contained no errata entry for this C.II proposition. This is a limited
search, not a claim that no errata exist.

The Lean proof takes a different route. It applies the published
Noetherian localization core, whose surjectivity step is a quotient
Hopfian argument. Its kernel step stabilizes the ascending chain of power
kernels. Neither step uses commutativity. The acting ring `A` may be
noncommutative and nonunital. Its original action may be degenerate,
for example zero, and the group `V` may be zero.

The proof covers exactly the three published internal targets. It does
not compare them with Renard's finite-type or Noetherian conventions. It
does not prove the complete source-facing C.II proposition or identify
the localization with the stable image. The complex-compatible,
ordinary-ring, power, criteria, quotient, universal-property and
unitization-finiteness branches are untouched, as is the additive
stable-image statement task. All of these remain separate obligations.

## Generic helpers and local module selection

The helpers are stated over an arbitrary commutative scalar ring `k`.
They take a nonunital ring `A` with `Module k A`, `IsScalarTower k A A`
and `SMulCommClass k A A`. They also take an additive group `V` with
`Module k V`, an action `ρ : A →ₙₐ[k] Module.End k V` and an actual
self-intertwiner `g : LinearIntertwiner ρ ρ`. Finally they take the
commutation proof `ha` for `g.toLinearMap` and `ρ`. Put
`U = Unitization k A` and `a = g.toLinearMap`. They use the actual
`Localized a`, `iota a`, `localizedEnd a`, `localizedInv a` and
`localizedAction a ρ ha`.

The source module on `V` is exactly `CompatibleUnitization.module ρ`.
On `Localized a` it is exactly
`CompatibleUnitization.module (localizedAction a ρ ha)`. Both are selected
locally, by `letI` in helper types and by `let` inside proofs. No global
instance is added. The surjectivity helper's type selects only the
localized action. Its proof adds the source action internally to form the
unitized maps, so the first target has no hypothesis on `V`.

The scalar module on `Localized a` is the existing generic one, found by
instance search at the generic ring `k`. The proof does not name the
statement's private alias `actualLocalizedScalarModule`. That alias has
body `inferInstance` at a generic ring, so at `k = ℤ` both select the same
module. The aggregate theorem is checked against the target type, so the
selections agree.

The proof uses three actual unitized maps. Each comes from a published
linear intertwiner by `CompatibleUnitization.ofLinearIntertwiner`, and
has the same underlying function as that intertwiner.

- `G = ofLinearIntertwiner g : Module.End U V`, the unitized source
  endomorphism.
- `F = ofLinearIntertwiner (iotaIntertwiner a ρ ha) : V →ₗ[U] Localized a`,
  the unitized canonical map.
- `E = unitizedLocalizationEquiv a ρ ha`, a `U`-linear automorphism of
  `Localized a`, built with `LinearEquiv.ofLinearMap`. Its two maps come
  from `localizedEndIntertwiner` and `localizedInvIntertwiner`. Its
  inverse laws are the published `localizedEnd_localizedInv` and
  `localizedInv_localizedEnd`.

## Implemented proof

**Power coherence.** `unitizedLocalizationEquiv_pow_apply` shows that
`(E ^ n) y = (localizedEnd a ^ n) y`. `unitizedSelf_pow_apply` shows that
`(G ^ n) x = (a ^ n) x` for every `n` and `x`. Both proofs rewrite each
power as a function iterate with `LinearEquiv.pow_apply` or
`Module.End.pow_apply`. They close by definitional equality of the
underlying functions.

**Core certificates.** `unitized_intertwines_exhausts` proves the
intertwining identity `F (G x) = E (F x)` from the published
`iota_intertwines`. It also proves inverse-power exhaustion. Every element
of `Localized a` is an actual fraction `frac a x n` by `frac_surjective`.
By power coherence and `localizedEnd_pow_frac`, `E ^ n` sends
`frac a x n` to `iota a x = F x`.

**Surjectivity helper.** `surjective_of_isNoetherian_unitized` assumes
only `IsNoetherian U (Localized a)` for the localized action. It applies
the published `NoetherianLocalizationCore.exhaustion_surjective` with
ring `U`, source `V`, target `Localized a`, and the maps `G`, `E` and `F`.
Surjectivity of `F` is surjectivity of the actual `iota a`, since the
functions coincide.

**Stabilization helper.** `stabilization_of_isNoetherian_unitized`
assumes Noetherianity of both selected unitized modules. Local nilpotence
of the kernel comes from the published `iota_eq_zero_iff`. If
`iota a x = 0`, it gives some `m` with `(a ^ m) x = 0`, hence
`(G ^ m) x = 0` by power coherence. The published
`NoetherianLocalizationCore.localization_core` then returns surjectivity
of `F`. It also returns one exponent `n > 0` for which, as
`U`-submodules, `ker F = ker (G ^ n)`, `ker (G ^ n) = ker ((G ^ n) ^ 2)`
and `range (G ^ n) = range ((G ^ n) ^ 2)`. The same `n` is used for every
remaining conjunct.

The conclusion concerns `k`-linear kernels and ranges of `iota a`, `a ^ n`
and `(a ^ n) ^ 2` in `V`. Power coherence gives `(G ^ n) x = (a ^ n) x`.
Expanding both squares as composites then gives
`((G ^ n) ^ 2) x = ((a ^ n) ^ 2) x`, and `F x` is definitionally
`iota a x`. Each equality is proved by extensionality. Membership in the
`k`-linear kernel or range is rewritten along these identities into
membership in the corresponding `U`-submodule.
The core's equality then applies. Only underlying sets are compared, so
the change of scalar ring is harmless.

**Finite helper.** `stabilization_of_finite_unitized` assumes
`IsNoetherianRing U`, `Module.Finite U V` and
`Module.Finite U (Localized a)` for the selected actions. Mathlib's
`isNoetherian_of_isNoetherianRing_of_finite` holds over arbitrary unital
rings, so it gives both module Noetherian hypotheses. The proof then
applies the stabilization helper.

**Aggregate.** `additiveLocalizationNoetherian` specializes the helpers
at `k = ℤ`. For each target it introduces the acting ring, the group,
their instances and the original `f : NonUnitalModuleHom A V V`. It takes
`ρ` to be the canonical integer action
`NonUnitalModule.toIntLinearEndHom (A := A) (V := V)`, inferred from the
type of `g = f.toIntLinearIntertwiner`. The
published `toIntLinearIntertwiner_toLinearMap` holds by `rfl`, so
`g.toLinearMap` is definitionally the target's
`a = f.toAddMonoidHom.toIntLinearMap`. The compatibility proof is
`fun b v => f.map_smul b v`, the statement's own argument to
`localizedAction`. The three helpers are supplied in the published order.
`AdditiveLocalizationStabilizationAt f` unfolds to the helper's
conclusion at this data.

## Verification

The module compiled on 30 October 2026 in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with no errors or warnings.
Inspection of `additiveLocalizationNoetherian` reported a theorem with
level parameters `uA` and `uV`. It depends only on the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. It uses no `sorry`,
`admit` or new axioms. Development compilation is not acceptance.
Independent semantic review, the Lake build, exact-target validation and
Library publication are still required.
