# Proof of the canonical stable image for additive nonunital actions

Authors: Worker 490 and Worker 926. Worker 490 adapted their published
complex-compatible stable-image proof to the canonical integer conversion of
original additive data, following Worker 926's successor-task route. The
published target and all its imported Lean/Markdown pairs are unchanged.

The closed theorem
`Langlands.Renard.AdditiveActionLocalization.additiveStablePowerImageStatement`
has exactly type
`Langlands.Renard.AdditiveActionLocalization.AdditiveStablePowerImageStatement.{uA, uV}`.
The acting-ring universe `uA` and carrier universe `uV` are independent.
There are no external section parameters or additional premises.

## Source and scope

The motivating original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The final C.II proposition is on printed p. 279 / PDF p. 285; stability is
defined on printed p. 276 / PDF p. 282. Actual endomorphism localization is
A.III.1, example 5 and its following lemma and corollary, printed pp. 252–253 /
PDF pp. 258–259. The nonunital conventions are on printed pp. 5–6 / PDF
pp. 11–12, and the additive versus complex-linear Hom distinction and
unitization are I.2.1, printed p. 14 / PDF p. 20, with context on PDF p. 21.
Worker 490 read these passages for this proof on 30 October 2026 and visually
checked PDF p. 285; the source hash was verified.

The registered supplementary source `renard-2010-corrections-complements`,
at `/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked on PDF pp. 18–19 after verifying its hash. These pages do not
correct the final C.II proposition or resolve its nonunital finiteness
conventions. No dedicated source errata file was present in the project,
workspace or pinned Library. The 2026 original governs.

This proof is **internal derived, finiteness-free content**. Renard's final
proposition assumes a commutative Noetherian complex algebra, a finite module
and finite localization, and concludes eventual stability followed by the
stable-image identification. Here a positive stable power is supplied.
Canonical integer linearity, normalization of the inverse, and uniqueness
are derived refinements, not attributed to the source as stated. The proof
does not establish eventual stability, interpret the source's finiteness
conventions, or complete the source-facing final C.II proposition.

The acting ring `A` is an arbitrary `NonUnitalRing`, possibly noncommutative.
The carrier `V` is an additive commutative group with its original
`NonUnitalModule A V`, and `f : NonUnitalModuleHom A V V` is its original
additive self-intertwiner. No complex vector space, scalar compatibility
certificate, unit law, nondegeneracy, nontriviality, dimension or finiteness
assumption is added. Zero actions and zero carriers are included. Even when
`A = ℤ` acts by zero, the integer scalars of `V` remain the canonical scalars
of its additive group, independently of that original action.

## Published constructions

The proof imports
`Langlands.Algebra.RenardAdditiveStableImageStatements` and
`Langlands.Algebra.RenardLocalizationStabilityProof`.
It uses the existing actual `Localized a`, `iota a`, `localizedEnd a`,
`localizedAction`, `CompatibleUnitization` module and conversions,
compatible kernel/range, and restricted action by their published Lean names.
There is no replacement localization, action or power system.

Set `ρ = NonUnitalModule.toIntLinearEndHom (A := A) (V := V)` and
`a = f.toAddMonoidHom.toIntLinearMap`. The published
`f.toIntLinearIntertwiner` has underlying linear map `a` by definition.
The action-commutation proof is exactly `fun b v => f.map_smul b v`.
The actual localized action is `σ = localizedAction a ρ` with that proof.
Locally install `CompatibleUnitization.module ρ` and use exactly the target's
powers: convert `f.toIntLinearIntertwiner` to an endomorphism of that module,
raise it to the given exponent, and convert back. Write `K` and `I` for its
compatible kernel and range at `n`.

The private generic abbrev `AdditiveStableImageProof.localizedScalarModule`
selects the existing module of the generic localization before specialization
to integers. Installing it locally in the proof retains the same localization
module argument as the target. It creates no new action or global instance.
This prevents integer typeclass inference from selecting the separately
constructed canonical integer module of the localized additive group. The
proof unfolds `AdditiveStablePowerImageAt`; it does not refer to the target's
private alias. Integer structures on the compatible submodule carriers are
the ones used by the published target and restriction maps.

## Implemented proof

The three public helper theorems are in namespace
`Langlands.Renard.AdditiveActionLocalization.AdditiveStableImageProof`.

1. `powers_toLinearMap` works for any integer-linear self-intertwiner of
   `ρ`. It proves that the underlying map of every converted unitized power
   is the corresponding ordinary power. The zero case is reflexive. For a
   successor, extensionality, `pow_succ` and `Module.End.mul_apply` reduce
   the assertion to the induction hypothesis evaluated at `f x`.

2. `isCompl_of_toSubmodule` reflects complementarity from integer submodules
   to the compatible-submodule lattice. Rewrite disjointness and codisjointness
   as the infimum and supremum equations. The injective `toSubmodule` map,
   and its preservation of infimum, supremum, bottom and top, give both
   required equations.

3. `additiveStablePowerImageAt_of_stable` takes only `0 < n` and the two
   stability equalities for `a ^ n`. After unfolding the target's local
   definitions, power coherence identifies `K.toSubmodule` with
   `ker (a ^ n)` and `I.toSubmodule` with `range (a ^ n)`.
   The published `EndomorphismLocalization.stablePowerImageStatement` at
   coefficient ring ℤ supplies ordinary complementarity and an equivalence
   `e₀` whose inverse is the actual canonical map on `range (a ^ n)`.
   The second helper transfers complementarity to `K` and `I`.

   Put `g = (iota a).comp I.toSubmodule.subtype`. The inverse equation for
   `e₀` implies bijectivity of the canonical map on the ordinary range.
   Compose that bijection with `LinearEquiv.ofEq` for the equality of the
   underlying submodules to obtain bijectivity of `g`; this comparison is
   made at the level of functions. Define
   `e = (LinearEquiv.ofBijective g _).symm`. Its inverse is `g` by definition,
   proving the required inverse-map equation.

   For action compatibility, apply the injective `e.symm`. The inverse
   formula and `CompatibleSubmodule.restrictAction_apply_coe` reduce the
   equation to `localizedAction_iota a ρ` and the inverse law. This proves
   `e (σ b z) = I.restrictAction b (e z)` for every original ring element
   `b` and localized vector `z`.

   For operator compatibility, first show that `I.toSubmodule` is invariant
   under `a`. Under the ordinary-range identification, the witness for
   `a ((a ^ n) y)` is `a y`, because `a ^ n * a = a * a ^ n`.
   Thus `a (e z)` belongs to that subtype. Apply `e.symm` and use
   `iota_intertwines` to prove
   `e (localizedEnd a z) = ⟨a (e z), _⟩`.
   Taking underlying vectors gives exactly the target's equation of
   composite linear maps.

   Finally, any equivalence `e'` satisfying the three equations has
   `e'.symm.toLinearMap = g = e.symm.toLinearMap`. Injectivity of the map
   to underlying linear maps and of taking inverses gives `e' = e`.
   Uniqueness follows from the inverse equation alone; all three equations
   remain inside the unique-existence predicate.

The closed theorem introduces exactly the published target's original data,
exponent, canonical map `a`, positivity and two stability equalities, and
applies the third helper. Complementarity, bijectivity, compatibility and
uniqueness are proved rather than assumed.

## Development checks

In approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, the complete
proof compiled with zero errors and warnings and its closed theorem was
inspected. Its only axioms are `propext`, `Classical.choice` and `Quot.sound`.
A private inspection overlay checked all public helper types, the unapplied
closed theorem and its exact target at arbitrary independent `uA, uV`, and
at `(0, 1)` and `(1, 0)`. All checks passed. The target's complete project-import closure, 22 Lean/Markdown
files, was compared byte for byte with the published Library base and is
unchanged. Independent semantic acceptance and official machine validation
are separate from these development checks.
