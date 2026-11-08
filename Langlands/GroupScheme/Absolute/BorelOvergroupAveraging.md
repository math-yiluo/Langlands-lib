# Integral cocharacters presenting root support

This internal construction is a conditional step toward the absolute
Borel-overgroup cocharacter statement. Worker 146 supplied the integral averaging
argument and the support-preserving negator interface; Worker 1272 implemented
the Lean proof. The argument combines the published integral Weyl actions,
invariant lattice pairing, actual root permutation, reductive Weyl finiteness
and root-negation theorem. It uses no simple-root classification.

For a field `k : Type u`, an affine group scheme `G`, a commutative group scheme
`T`, and an underlying monomorphism `j : T.toGrp ⟶ G`, the definition
`AbsoluteBorelOvergroup.rootSupportStabilizer j S` is the subgroup of the actual
relative Weyl quotient `relativeWeylGroup j` consisting of all classes `w` such
that, for every actual root `α` of `j`,

`relativeWeylCharacterAction j w α ∈ S ↔ α ∈ S`.

Here `S` is any set of integral characters of `T`. Membership of nonroot
characters is unrestricted. The Weyl action permutes the actual roots, so these
classes form a subgroup: composition preserves membership by two equivalences,
and the inverse condition follows by applying the original condition to the
inverse image of a root.

The theorem `exists_cocharacter_of_finite_rootSupport_negators` assumes:

- The actual Weyl quotient is finite, and actual roots are stable under negation.
- An actual integral cocharacter `ν` is generic, meaning that its pairing with
  every actual root is nonzero.
- Every actual root with strictly positive pairing with `ν` belongs to `S`.
- For every actual root `α` for which both `α` and `-α` belong to `S`, an actual
  Weyl class preserves membership in `S` on all roots and sends `α` to `-α`.

It produces an actual integral cocharacter `ζ` such that every actual root `α`
satisfies `α ∈ S ↔ 0 ≤ latticePairing T α ζ`.

The proof sets `H = rootSupportStabilizer j S` and takes the finite sum
`ζ = ∑ w : H, relativeWeylCocharacterAction j w.val ν`.
This is already an integral cocharacter; there is no division by the order of
`H`. Left multiplication permutes `H`, so every element of `H` fixes `ζ`.

If a root `α` is absent from `S`, the inverse image of `α` under each element of
`H` is again a root absent from `S`. Its pairing with `ν` is nonzero by
genericity and cannot be positive by the positive-root inclusion, so it is
strictly negative. Invariance of the lattice pairing moves the Weyl action
from the cocharacter to this inverse image. Every term in the pairing with the
orbit sum is therefore negative; the sum is strictly negative because `H`
contains the identity.

If both `α` and `-α` belong to `S`, a supplied negator fixes `ζ` and negates
`α`. Pairing invariance then identifies the pairing with its negative, so it is
zero. If `α` belongs to `S` but `-α` does not, the preceding negative-pairing
argument applied to the root `-α` makes the pairing with `α` strictly positive.
These cases prove the exact nonnegative-pairing equivalence.

The wrapper `exists_cocharacter_of_rootSupport_negators` assumes that `G` is
connected reductive and that `j` is a specified split maximal torus. It
discharges finiteness with
`IsConnectedReductive.finite_relativeWeylGroup_of_isMaximalTorus` and root
negation with `neg_mem_roots_of_split_maximalTorus`, retaining the generic
cocharacter, positive-root inclusion and support-preserving negators as explicit
inputs. These are proved Library theorems, independent of the prohibited
split-parabolic cocharacter and parabolic-intersection classification chain.

All fields and characteristics and the original universe are retained. No
nonempty-root, positive-rank, proper-support or nonzero-output condition is
imposed. The empty-root and rank-zero cases are included. This module neither
constructs the initial generic cocharacter and negators for a given Borel
overgroup nor proves the host unconditional cocharacter-existence statement;
those remain separate obligations.
