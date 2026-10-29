# Proof of the canonical compatible stable image

Authors: Worker 490 and Worker 926. This internal derived proof imports the
published `CompatibleStablePowerImageStatement` unchanged. Its implementation
adapts Worker 926's privately checked proof, whose SHA256 was verified before
reuse. The final English proof description and public module are prepared by
Worker 490.

The closed theorem
`Langlands.Renard.AlgebraActionLocalization.compatibleStablePowerImageStatement`
has exactly the type
`Langlands.Renard.AlgebraActionLocalization.CompatibleStablePowerImageStatement.{uB, uV}`.
The algebra universe `uB` and vector-space universe `uV` are independent.
There are no external section parameters or additional hypotheses.

## Source and scope

The original motivation is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix C.II,
final proposition and proof, printed p. 279 / PDF p. 285. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The definition of stability is on printed p. 276 / PDF p. 282. Actual
endomorphism localization and its algebra-action extension are A.III.1,
example 5, printed p. 252 / PDF p. 258, followed by the kernel description
on printed p. 253 / PDF p. 259. The nonunital ring and action conventions
appear on printed p. 6 / PDF p. 12.

Worker 490 read these pages and visually inspected PDF p. 285. The older
registered supplementary source `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp. 18–19, was also read; those pages contain no correction to the
final C.II proposition. No separate project errata note for the 2026 source
was found. The 2026 text governs.

Renard assumes a commutative Noetherian complex algebra, a finite module
and a finite localization, then derives eventual stability and identifies
the localization with every positive stable image. This proof establishes
the already published **internal finiteness-free refinement** of only the
identification clause: a positive stable power is given. The algebra may
be noncommutative and nonunital; its compatible action may be zero or
degenerate and need not obey a unit law. The space may be zero or infinite
dimensional. Canonical normalization and uniqueness are internal derived
refinements, as explained in the target's Markdown. This unit adds no
finiteness, Noetherianity, finite-dimensionality or nontriviality hypothesis.
It does not prove the source's eventual-stability assertion under its
finiteness assumptions or complete the general C.II proposition.

## Published dependencies

The two direct imports are
`Langlands.Algebra.RenardCompatibleStableImageStatements` and
`Langlands.Algebra.RenardLocalizationStabilityProof`.
The first supplies the exact target and the actual compatible algebra
constructions. The second supplies the ordinary unital-module theorem
`Langlands.Renard.EndomorphismLocalization.stablePowerImageStatement`,
used at coefficient ring ℂ. Its stable-image conclusion requires only
positivity and equality of the kernels and ranges with those of the square;
its separate Noetherian conclusions are not invoked.

The carrier `Localized a`, canonical map `iota a`, operator `localizedEnd a`,
action `localizedAction a ρ ha`, compatible kernel/range/restricted action,
and the local `CompatibleUnitization` module and conversions are all the
published constructions. The target pair and every pair it imports remain
unchanged. No alternative localization or assumed comparison is introduced.

## Implemented proof

The three helper theorems are in namespace
`Langlands.Renard.AlgebraActionLocalization.CompatibleStableImageProof`.
Write `a = f.toLinearMap` for the given self-intertwiner `f` and let `n > 0`
satisfy `Stable (a ^ n)`. Let `powers` be exactly the target's powers: convert
`f` to a unitized module endomorphism, take its monoid power, and convert
back under the local `CompatibleUnitization.module ρ`.

1. `powers_toLinearMap` proves `(powers m).toLinearMap = a ^ m` for every
   natural `m`. At zero the identity maps agree by definition. For the
   successor, evaluate both maps, expand `pow_succ` and composition using
   `Module.End.mul_apply`, and apply the induction hypothesis at `f x`.
   This uses the published powers rather than defining a new power system.

2. `isCompl_of_toSubmodule` reflects complementarity through the injective
   forgetful map from compatible submodules to complex subspaces. It rewrites
   disjointness and codisjointness as the infimum and supremum equations and
   uses `toSubmodule_inj` together with `inf_toSubmodule`, `sup_toSubmodule`,
   `bot_toSubmodule` and `top_toSubmodule`.

3. `compatibleStablePowerImageAt_of_stable` unfolds the target's actual local
   definitions. Power coherence identifies the underlying spaces of
   `K = (powers n).ker` and `I = (powers n).range` with `ker (a ^ n)` and
   `range (a ^ n)`. The ordinary theorem supplies complementarity and an
   equivalence `e₀` whose inverse is `iota a` restricted to `range (a ^ n)`.
   The previous helper transfers complementarity to the compatible lattice.

   Put `g = (iota a).comp I.toSubmodule.subtype`. The inverse equation for
   `e₀` proves bijectivity of the canonical map on `range (a ^ n)`.
   Composing it with `LinearEquiv.ofEq` for the underlying-space equality
   proves bijectivity of `g`. Define `e = (LinearEquiv.ofBijective g _).symm`.
   Its inverse is `g` by definition, so the required canonical equation is
   proved directly, rather than assumed.

   For action compatibility, apply the injective `e.symm` to the desired
   equality. Its formula and `restrictAction_apply_coe` reduce the assertion
   to `localizedAction_iota a ρ ha b (e z)`, followed by the inverse law.
   This proves the actual B-action equation for every `b` and `z`.

   For operator compatibility, first show that `I.toSubmodule` is invariant
   under `a`: in `range (a ^ n)`, this follows from
   `a ^ n * a = a * a ^ n`. Thus `a (e z)` defines an element of that subtype.
   Applying `e.symm` and using `iota_intertwines` proves
   `e (localizedEnd a z) = ⟨a (e z), _⟩`. Taking underlying vectors gives
   exactly the target's composite linear-map equation.

   For uniqueness, an equivalence `e'` satisfying all three equations has
   `e'.symm.toLinearMap = g = e.symm.toLinearMap` from its third equation.
   Injectivity of the map to underlying linear maps and injectivity of
   taking inverses give `e' = e`. The first two conditions remain inside the
   unique-existence predicate even though uniqueness needs only the third.

The closed theorem introduces exactly the target's algebra, scalar
compatibility instances, vector space, action, self-intertwiner, exponent,
positivity and stability assumptions, and applies the third helper. The
ordinary theorem is applied to the two conjuncts of the published `Stable`
definition. No complementarity, surjectivity, equivalence, compatibility or
uniqueness conclusion is taken as an extra premise.

## Development checks

In approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Worker 490
compiled the complete proof with zero errors and zero warnings and inspected
the closed theorem. It has independent level parameters `uB uV` and depends
only on `propext`, `Classical.choice` and `Quot.sound`. A separate excluded
private overlay printed the complete unapplied theorem type and checked its
exact target at arbitrary `uB, uV` and at both `(0, 1)` and `(1, 0)`.
All checks passed. The target and its project-import closure, 22 Lean/Markdown
files, were compared byte for byte with the published Library base and are
unchanged. The cited original and supplementary errata hashes were verified.
These are development checks; independent semantic acceptance and official
candidate validation remain separate requirements.
