# Finite degree-zero Brauer induction

Worker 1787 proves
`Langlands.FiniteRep.DegreeZeroBrauer.finiteDegreeZeroBrauer` with type
`FiniteDegreeZeroBrauerStatement G` for every finite group `G : Type uG`.
The group universe remains arbitrary. There are no further mathematical
premises. The statement and the constructions it imports are unchanged.

The result is an equality of integer submodules of the genuine split
representation group `VirtualRep ℂ G`: the span of actual subgroup inductions
of differences of two scalar rank-one classes equals the kernel of the actual
virtual character evaluated at the identity. The proof establishes both
inclusions, and the intermediate character image is compared back to that
same split group.

## Centering and the exact character image

The internal integer-linear map `augment G` sends a function `f` to
`g ↦ f g - f 1`. The supporting module defines `characterSpan G` as the image
of `degreeZeroBrauerSpan G` under the actual virtual-character map; membership
therefore supplies a genuine virtual representative belonging to the required
span. Its proved adapters compare normalized character induction `ind` with
actual `virtualInduce`, and preserve this image under subgroup induction and
pullback along a surjective group homomorphism.

`ind_at_one` evaluates the normalized induction sum at the identity. Since a
scalar character has value one there, `augment_ind_scalar` expresses its
centered induction as the sum of an induced scalar-character difference and
the centered permutation character `augment G (ind S 1)`.

If a normal subgroup `A` is contained in `S`, the subgroup `S/A` of `G/A`
pulls back exactly to `S`. `augment_permutation_mem` applies the supporting
inflation formula to identify `ind S 1` with the pullback of the actual
permutation character induced from `S/A`. Hence the degree-zero result for
actual characters on `G/A` supplies this centered permutation character.
`augment_monomial_mem` applies that reduction to a finite monomial list in
which every inducing subgroup contains `A`.

## Induction on finite group order

The initial argument uses groups and representation carriers in `Type 0`.
`augment_of_normal` applies the retained-subgroup monomial engine to a normal
abelian nontrivial subgroup `A` for which every group element has a p-power
in `A`, with p prime. The quotient has strictly smaller order, since
`|G| = |G/A| |A|` and `|A| > 1`. The inductive assertion for `G/A`, followed
by the preceding monomial reduction, gives the centered character assertion
for `G`.

`augment_of_hyper` handles the structural data of a hyperelementary group.
If its cyclic normal subgroup `C` is nontrivial, it serves as `A`. If `C` is
trivial, the power condition makes `G` a p-group. For a nontrivial finite
p-group its center is nontrivial; that center serves as `A`. It is normal and
abelian, and every group element has a p-power equal to one. These facts use
Mathlib's proved finite p-group center theorem. The coprimality part of the
Solomon structural witness is not needed in this reduction.

`augment_native` performs strong induction on `Nat.card G`, with the trivial
group handled by the vanishing of every centered function. The published
Solomon theorem gives an integral identity

```text
1 = Σ aᵢ Ind(Hᵢ, 1).
```

If one `Hᵢ` is all of `G`, its structural witness gives the preceding
hyperelementary case. Otherwise all `Hᵢ` are proper. The proved character
projection formula `ind_augment_restrict` multiplies this identity by the
centered character to obtain

```text
augment(character V)
  = Σ aᵢ Ind(Hᵢ, augment(character (V restricted to Hᵢ))).
```

Character conjugacy invariance proves this formula directly in the normalized
sum. Each restricted representation lies on a group of strictly smaller
order, so strong induction and `ind_mem` place the entire integer sum in the
exact character image. No degree-zero generation or monomiality conclusion
is assumed as a premise.

## Arbitrary universes and the genuine group

`augment_character_mem` chooses a finite group in `Type 0` isomorphic to the
original `G`. It pulls the actual action to that group, applies
`augment_native`, and transports back with the proved surjective-pullback
adapter. The transported character equals the original character pointwise.
Thus the restriction to `Type 0` is internal to the proof.

`span_le_degreeZero` proves the elementary inclusion directly. The actual
induction-character formula and `ind_at_one` show that each generating
rank-one difference has value zero at the identity. Linearity extends this
to its integer span.

For the reverse inclusion, `degreeZero_le_span` writes an arbitrary genuine
virtual class `x` as the difference of two actual classes. The centered
character assertion for each actual representative puts
`augment (virtualCharacter x)` in `characterSpan G`. Degree zero makes this
function equal to `virtualCharacter x`. By the definition of `characterSpan`
there is a genuine `y` in the required span with the same virtual character
as `x`. The published theorem `VirtualCharacter.faithfulness` gives `y = x`.
This proves the desired generation inclusion in `VirtualRep ℂ G` itself.
The final theorem combines the two inclusions by antisymmetry.

## Source and proof route

The target corresponds to Deligne, *Les constantes des equations
fonctionnelles des fonctions L* (1973), Proposition 1.5, printed p.510 /
PDF p.10, with the conventions on pp.507–509. Registered source:
`deligne-1973-local-constants`, SHA-256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
The statement's paired Markdown explains its specialization to complex
coefficients and its use of all subgroups and rank-one pair differences.

This implementation uses the Solomon and retained-normal-subgroup monomial
route. Solomon's identity is imported by Lean name from the published
Anthropic FLT port; the retained-subgroup engine and induction adapters are
in the separate supporting modules `DegreeZeroMonomial` and
`DegreeZeroBrauerSupport`. Original-source attribution and the changes to
the monomial engine are documented in that module. The present proof is a
derived composition of these proved results and Mathlib's group and
representation theory. It uses no unproved classification, generation,
faithfulness, or exact-to-split representation-group comparison premise.
