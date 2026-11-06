# Finite degree-zero Brauer induction

Worker 1749 states `Langlands.FiniteRep.FiniteDegreeZeroBrauerStatement`
for every `G : Type uG` with `[Group G] [Fintype G]`. The group universe is
arbitrary; coefficients are the actual complex numbers. This is a proposition
definition, with no proof of the generation theorem.

## Objects and exact statement

The ambient group is the existing `VirtualRep ℂ G`, the split additive
Grothendieck group of actual finite-dimensional representation isomorphism
classes. The module imports `Langlands.Representation.Finite.Virtual` and
reuses its constructions by Lean name.

`virtualDegree G` is the integer-linear map
`x ↦ virtualCharacter x 1` with codomain `ℂ`, regarded as a module over `ℤ`.
It composes character realization with Mathlib's linear projection at the
identity. `degreeZeroVirtualReps G` is its kernel inside `VirtualRep ℂ G`.

For actual representations `V` and `W`, evaluation on their virtual
difference has the meaning

```text
virtualDegree G (ofClass (classOf V) - ofClass (classOf W))
  = (finrank ℂ V : ℂ) - (finrank ℂ W : ℂ).
```

This follows from `virtualCharacter_ofClass`, `character_classOf`,
`FDRep.char_one`, and linearity. Every virtual representation is a difference
of actual classes by `virtualRep_exists_difference`. Its integral virtual
dimension is therefore `finrank ℂ V - finrank ℂ W`, with both natural
dimensions cast to `ℤ`. Direct-sum additivity and isomorphism invariance make
this integer independent of the chosen difference. Its cast to `ℂ` is exactly
`virtualDegree G x`. Since the integer cast into `ℂ` is injective, membership
in this kernel is equivalent to integral virtual dimension zero.
This explains the kernel's meaning without requiring character faithfulness.

`degreeZeroBrauerGenerators G` is exactly the set

```text
{ x | ∃ (S : Subgroup G) (χ χ' : S →* ℂˣ),
    x = virtualInduce S
      (ofClass (classOf (oneDimensional χ)) -
       ofClass (classOf (oneDimensional χ'))) }.
```

Here `oneDimensional χ` is the actual scalar action on `ℂ`, and
`virtualInduce S` extends the actual finite-index quotient induction
additively to the split group. Finiteness of `G` supplies finite index for
every subgroup. `degreeZeroBrauerSpan G` is `Submodule.span ℤ` of this set;
the coefficients are integers and supports are finite.

`FiniteDegreeZeroBrauerStatement G` asserts
`degreeZeroBrauerSpan G = degreeZeroVirtualReps G`. Thus it asserts both that
these induced differences have degree zero and that every genuine virtual
representation of degree zero is an integral combination of them.

## Original source and translation

Pierre Deligne, *Les constantes des equations fonctionnelles des fonctions L*,
in *Modular Functions of One Variable II*, Lecture Notes in Mathematics 349
(1973), pp.501–597:

- Literature ID: `deligne-1973-local-constants`.
- SHA-256: `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
- Retained source:
  `/home/taskhub/central-library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`.
- Section 1.1, printed pp.507–508 / PDF pp.7–8, defines the representation
  Grothendieck group, its integer dimension, induction, and scalar characters.
- Proposition 1.5, printed p.510 / PDF p.10, with the finite-group and
  root-of-unity conventions on p.509 / PDF p.9, is the degree-zero induction
  assertion. The original pages 507–511 were read, and Proposition 1.5 and
  its displayed argument were inspected in the page image.

Deligne assumes the coefficient field contains the requisite roots of unity;
`ℂ` satisfies this condition. His conclusion uses elementary subgroups and
dimension-zero virtual integer combinations of rank-one representations.
If such a combination is `∑ nᵢ[χᵢ]`, its dimension is `∑ nᵢ`. When this sum
vanishes, it equals `∑ nᵢ([χᵢ] - [1])`. Conversely each difference of two
rank-one classes has dimension zero. Additivity of actual induction therefore
translates the source's generators into the pair differences used here.

Allowing all subgroups gives the consequent needed for the common-closure
degree-zero generation consumer. The reverse inclusion has the usual
dimension interpretation: induction multiplies the source dimension by the
subgroup index. This discussion explains the source correspondence; it does
not supply a Lean proof of either inclusion.

Deligne's source group uses exact-sequence relations. Over a finite group
and `ℂ`, complete reducibility gives the mathematical comparison with the
split representation group used here. This module states the conclusion
directly on the existing split group; it constructs or assumes no split-to-exact
comparison. A proof using that comparison must establish it separately.

The named submodules and evaluation map are internal packaging of these
existing constructions. No Brauer theorem, generation assertion,
classification result, character-faithfulness assertion, or identification
with the character image is an assumed premise. The finite degree-zero
generation equality remains a separate proof obligation.
