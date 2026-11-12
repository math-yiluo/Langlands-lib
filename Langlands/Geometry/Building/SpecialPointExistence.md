# Special points of affine root systems, including rank zero

`AffineRootSystem.IsAffineRootSystemWithRankZero.exists_isSpecialPoint`
proves that a set of affine roots satisfying the Library's rank-zero-compatible
axioms has a special point in its original affine space. The translation space
and the affine space have independent, arbitrary universes. Neither reducedness
nor a positive-rank assumption is imposed.

Here specialness means the published `IsSpecialPoint` predicate: every affine
root hyperplane is parallel to a root hyperplane through the chosen point. The
module proves this predicate directly. It does not assert an
`IsExtraSpecialPoint` conclusion.

## The finite derivative root pairing

Finiteness and spanning of the derivative roots imply finite dimensionality of
the dual translation space, and hence of the translation space, using
`Module.Finite.of_fg_top` and `Module.finite_dual_iff`.

For each derivative root `a`, `derivativeRootLift` chooses an affine root with
derivative `a`, and `derivativeCoroot` chooses its AR 2 coroot. AR 2 shows that the
associated reflection preserves the derivative root set.
`Module.eq_of_mapsTo_reflection_of_mem` shows that two derivative roots with
the same chosen coroot coincide. Thus these coroots form an embedding.
`RootPairing.mk''` constructs `derivativePairing`, paired by evaluation between
the dual translation space and the translation space. AR 3 supplies its
`IsCrystallographic` instance. These are auxiliary constructions for the proof,
on the supplied roots and spaces.

## Common zero and specialness

Choose a real linear functional `f` nonzero on every derivative root, using
`Module.exists_dual_forall_apply_ne_zero`. Let the simple indices be the positive
additively indecomposable roots, `IsAddIndecomposable.baseOf`.
`RootPairing.linearIndepOn_root_baseOf'` proves their linear independence without
requiring the root system to be reduced. The positive-root additive closure
theorem, together with negation, shows that these simple roots span the dual
translation space. They therefore form a linear basis.

Choose any origin `p` in the affine space. Define a functional on that basis
whose value at a simple derivative is the negative of its chosen affine lift's
value at `p`. `Basis.constr` extends these values, and `Module.evalEquiv`
represents this functional by a translation vector `v`. The point `v +ᵥ p`
is a common zero of all chosen simple affine lifts.

The rest of the proof is a finite descent on positive derivative roots. A
positive root pairs positively with some simple coroot. Reflecting in this
simple root strictly decreases its `f`-value. If the reflected root is negative,
linear independence and the nonnegative simple-root expansions show that the
original root is proportional to that simple root. Otherwise one descends to a
smaller positive root. A minimal counterexample argument makes this termination
precise, using finiteness of the derivative root set.

Apply this descent to the set of derivative roots whose kernel equals the
kernel of a root vanishing at `v +ᵥ p`. It contains every direction proportional
to a simple root and is closed under negation. It is also stable under simple
reflections: each chosen simple affine reflection fixes the point, AR 2
preserves affine roots, and precomposing a vanishing root by that reflection
transports its derivative kernel. Thus every derivative direction occurs among
the roots vanishing at the point. The published `isSpecialPoint_iff_ker`
converts this conclusion into geometric specialness.

This construction also covers the empty derivative root set. Its simple basis
is empty, derivative spanning makes the translation space zero, and the
specialness assertion is vacuous. No selection of an affine root is evaluated
in that case. The AR 4 fields are not needed by this proof.

## Provenance and sources

The construction is a proof of the special-point existence consequence of
Kaletha–Prasad Proposition 1.3.43(1)–(2). It follows the common-zero construction
in part (1), then proves specialness by finite simple-root descent instead of
using the Weyl-group stabilizer criterion of Lemma 1.3.42.

The private descent lemmas adapt the coordinate-functional, positive-pairing,
and minimal-root arguments already implemented in the published Library module
`Langlands.Group.RootPairingWeylGeneration`. They are proved here as local helpers;
that module's final Weyl-generation theorem is not a premise. The construction
of the derivative pairing and the affine kernel-transport argument are derived
from the existing affine-root-system definitions and Mathlib results named above.

- Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Definition 1.3.1,
  Remark 1.3.2 and Proposition 1.3.3 (printed pp.14–15 / PDF pp.45–46);
  Definition 1.3.39 (printed p.29 / PDF p.60); Proposition 1.3.43(1)–(2)
  (printed p.30 / PDF p.61). Registered source
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024, PDF p.2:
  the infinite-fibre addition to AR 4, already present in
  `IsAffineRootSystemWithRankZero`. Registered source
  `kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
