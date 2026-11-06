# Reflecting a fixed-coweight character comparison to the splitting field

Author: Worker 1632.

This internal module allows the actual cocenter character comparison to be
verified over a further field while retaining the original splitting field,
the same integral coweight, and the ordinary Galois actions in the descent
conclusion.

`characterLattice.coweight_character_comparison_baseChange_iff` concerns an
actual homomorphism `f : T → Q` between split tori over any field `E`,
an integral root datum `P` on the actual lattices of `T`, and a supplied
coweight `ν`. For every field base map `b : Spec K → Spec E`, it identifies
the following assertions over `E` and `K`: actual character pullback is
injective, and its image is exactly the characters annihilating the coroots
whose roots evaluate to zero on the supplied coweight.

Over `K`, the datum is exactly `SplitRootDatum.baseChange b T hT P` and the
coweight is exactly `cocharacterLattice.baseChange b T ν`. Its integral
root evaluation equals the original evaluation, by the canonical root and
pairing formulas. Hence the same root-index subset selects the two
annihilators. The published coroot-character comparison under base change,
expanded by annihilator membership, proves the equivalence. The root-index
universe is independent of the field universe. No actual-root, reducedness,
finite-index or Galois hypothesis is needed for this first theorem.

`coweightCocenterRootDescentOfBaseChange` returns a genuine base `B` of a
supplied finite reduced actual root datum `P` for a split torus `T_E`
closed in an affine group `G_E`, where the torus map descends to `k`.
The ambient group over `k` is affine and locally of finite type. The actual
map `g : T → Q` also descends to `k`, and both `T_E` and `Q_E` are split.
The fields `k`, `E` and `K` have arbitrary common universe `u`.

The coweight `ν` is fixed by the ordinary cocharacter Galois representation
for `E/k`. The remaining comparison input is only over `K`: injectivity
and the full zero-root-coroot annihilator image for the actual iterated
base change of `g`, the canonically transported `P` and the canonically
transported same `ν`. The first theorem reflects this comparison to `E`.
`coweightCocenterRootDescent` then constructs `CocenterRootDescentData k E g`
for `B` and the simple subset `{p : B.support | P.root' p ν = 0}`.
All ordinary Galois actions and their correcting maps in this conclusion
are over `E/k`; no Galois structure or cocharacter fixedness over `K` is
assumed or inferred.

The provenance is this internal composition of the imported canonical
lattice and based-descent constructions. No literature theorem is
transcribed. Neither field extension needs to be finite, Galois, algebraic
or perfect. An algebraic closure can serve as the further field, but the
construction does not prove the required geometric character comparison
there, supply the actual root datum or fixed coweight, or choose any torus
or splitting field. These remain inputs to the unconditional root-model
proof.
