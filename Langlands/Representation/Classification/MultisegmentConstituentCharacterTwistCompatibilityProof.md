# Character twists of multisegment socles and Langlands heads

Authors: Worker 1715 (proof and original explanation); Worker 1598
(dependency verification and submission).

The theorem
`Langlands.Classification.multisegmentConstituentCharacterTwistCompatibility`
proves exactly the published proposition
`Langlands.Classification.MultisegmentConstituentCharacterTwistCompatibility.{uF,uV} F T`.
Its outer parameters are `{p : ℕ} [Fact p.Prime]`,
`(F : PadicField.{uF} p)` and `(T : F.TopologicalData)`, with independent
universes `uF` and `uV`.

Let `χ` be a character of `F^×` with open kernel. For every `n > 0`, every
multisegment `a` and every smooth complex representation `π` of
`GL_n(F)`, the theorem gives two biconditionals:

* `a` is the Zelevinsky socle multisegment of `π` if and only if `aχ` is that
  of `πχ`;
* `a` is the Langlands head multisegment of `π` if and only if `aχ` is that
  of `πχ`.

Here `aχ` is `a` with each segment's cuspidal base class twisted by `χ ∘ det`
and its length kept (the target's `twistSegment`). `πχ` is the smooth twist
of `π` by `χ ∘ det`. The hypothesis `0 < n` is not used.

This is an internal proof of the target, which is BZ77 Proposition 1.9(f)
applied to multisegment relations (see
[MultisegmentConstituentCompatibilityStatement.md](MultisegmentConstituentCompatibilityStatement.md)).
The segment-level input is the theorem
`segmentConstituentCharacterTwistCompatibility` in
`Classification.SegmentConstituentCharacterTwistCompatibilityProof`. Apart
from that, the proof uses only published constructions. The target and all
its imported Lean/Markdown pairs are unchanged.

## Characters and supercuspidal classes

General helpers:

* `isOpen_ker_mul_of_isOpen`: in a topological group, if two characters have
  open kernels, so does their product. Its kernel contains the intersection
  of their kernels (`Subgroup.isOpen_mono`).
* `isOpen_ker_inv_of_isOpen` and its `T.topology` form `isOpen_ker_inv_units`:
  `χ⁻¹` has the same kernel as `χ`.
* `supercuspidalClass_twist_comm`: two twists of a supercuspidal class
  commute. The proof uses the published `SupercuspidalClass.twist_twist` and
  `twist_congr` with `mul_comm`.
* `supercuspidalClass_twist_inv_twist`: twisting by `χ⁻¹` undoes twisting by
  `χ`. The proof uses `twist_twist`, `twist_congr` with `inv_mul_cancel`, and
  `twist_one`.

Then, with `χ` and its open kernel `hχ` on `F^×` fixed:

* `cuspidalCharacterTwist χ hχ ρ` keeps the rank of `ρ` and twists its class
  by `χ ∘ det`. Openness on `GL_r(F)` is the preimage of `hχ` under the
  continuous determinant `T.generalLinearDeterminant r`.
* `segmentCharacterTwist χ hχ Δ` twists the base and keeps the length. It is
  definitionally the target's `twistSegment Δ`.
* `cuspidalCharacterTwist_twist`: character twists commute with the real
  twists `ν^s`, by `supercuspidalClass_twist_comm` with the published open
  kernels of `T.determinantPowerCharacter`.
* `cuspidalCharacterTwist_inv_twist` and `segmentCharacterTwist_inv_twist`:
  twisting by `χ⁻¹` undoes the twist. Consequently the cuspidal twist is
  injective (`cuspidalCharacterTwist_injective`).
* `member_segmentCharacterTwist` and `support_segmentCharacterTwist`: the
  `i`th member of a twisted segment is the twisted `i`th member, and its
  support is the image of the original support.
* `precedes_segmentCharacterTwist`: twisting preserves `Segment.Precedes`.
  Linkedness transfers by taking images of supports, using injectivity for
  the two non-containments and `Set.image_union` for the union segment. The
  base relation transfers by `cuspidalCharacterTwist_twist`.
  `precedes_of_segmentCharacterTwist` reflects precedence by twisting with
  `χ⁻¹`.

## Twisted segment-product data

`datumCharacterTwist χ hχ d` is defined for a `SegmentProductDatum` `d`. It
keeps the length, twists every segment by `segmentCharacterTwist`, and
replaces block `i` by its smooth twist by `χ ∘ det` on its own
`GL_(deg Δ_i)(F)`. Segment degrees are unchanged by definition, so the same
`degree_sum` proof applies. The following hold:

* `datumCharacterTwist_shape`: the block shape is unchanged (`rfl`);
* `datumCharacterTwist_blocks`: the block actions are the twists (`rfl`);
* `datumCharacterTwist_induced`: the induced object is the normalized
  product-induction functor of `d.shape` applied to the twisted blocks
  (`rfl`);
* `multisegment_datumCharacterTwist`: the multisegment of the twisted datum
  is `d.multisegment` mapped by the segment twist (`Multiset.map_coe`,
  `List.map_ofFn`);
* `isPrecedenceOrdered_datumCharacterTwist`: precedence order is preserved,
  by the reflection of precedence.

`datumCharacterTwistInducedIso` is an isomorphism of smooth representations
from the twist of `d.induced` by `χ ∘ det` to the induced object of the
twisted datum. The proof first rewrites the target with
`datumCharacterTwist_induced`, so that both sides use the original shape
`d.shape`. It then applies `SmoothRep.mkIso` to the published
`T.normalizedProductDeterminantTwistEquiv d.shape ⟨χ, hχ⟩`, which multiplies
an induced function at `g` by `χ(det g)`.
`datumCharacterTwistInducedEquiv` is the corresponding equivalence of
actions, obtained by `SmoothRep.equivOfIso`.

## Forward direction and the closing proof

`characterTwist_forward χ hχ n a` says: let `π` and `π'` be smooth
representations of `GL_n(F)` with an equivalence from the `χ ∘ det` twist of
`π` to `π'`. If `a` is the Zelevinsky socle (resp. Langlands head)
multisegment of `π`, then `a` mapped by the segment twist is that of `π'`.

The proof unfolds the relation to a datum `d` with four properties:
`d.multisegment = a`, precedence order, every block a segment socle (resp.
head) of its segment, and `π` the irreducible socle (resp. head) of
`d.induced`. The witness is `datumCharacterTwist χ hχ d`:

* its multisegment and precedence order come from the two datum lemmas;
* each twisted block is a socle (resp. head) of its twisted segment by the
  first (resp. second) conjunct of
  `segmentConstituentCharacterTwistCompatibility`, applied with the
  determinant-preimage openness on `GL_(Δ.rank)(F)` and `GL_(Δ.degree)(F)`;
* the irreducible-socle (resp. head) condition comes from three steps:
  1. `isIrreducibleSocle_twist_iff` (resp. `isIrreducibleHead_twist_iff`)
     twists ambient and target together;
  2. `IsIrreducibleSocle.of_equiv` (resp. `IsIrreducibleHead.of_equiv`)
     transports the ambient along `datumCharacterTwistInducedEquiv`;
  3. `of_targetEquiv` from `SegmentHeadDecreasingSocle` (resp.
     `HeadTargetTransport`) transports the target along the given
     equivalence.

The closing theorem uses the forward direction twice:

* The forward implications use `π' = πχ` with the identity equivalence.
* For the reverse implications, `twist (χ⁻¹ ∘ det)` applied to `πχ` gives
  back `π.representation`, by `MonoidHom.inv_comp` and the published
  `twist_inv_twist`. Applying the forward direction to `χ⁻¹`, the twisted
  multisegment, `πχ` and `π` therefore gives relations for the multisegment
  twisted by `χ` and then by `χ⁻¹`. That multisegment is `a`, by
  `Multiset.map_map` and `segmentCharacterTwist_inv_twist`.

## Dependencies and scope

The direct imports are:

* the target module `Classification.MultisegmentConstituentCompatibilityStatement`;
* `Classification.SegmentConstituentCharacterTwistCompatibilityProof`;
* `Classification.HeadTargetTransport`;
* `Classification.SegmentHeadDecreasingSocle`.

The proof has no theorem-valued assumptions. It uses the actual data,
blocks, induced objects and intertwiners. It supplies no existence theorem
for socle or head multisegments.

The development check compiles the module in the prepared Lean 4.34.0
environment with no errors or warnings. The closing theorem's only axioms are
`propext`, `Classical.choice` and `Quot.sound`. Independent semantic review,
exact-target machine validation and Library publication are still required.
