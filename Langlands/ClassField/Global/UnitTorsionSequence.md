# The finite torsion exact sequence of arithmetic units

Let `F : Type u` and `E : Type v` be fields, with an `F`-algebra structure on
`E`, and put `G = E ≃ₐ[F] E`. The universes are independent. The action and
exact-sequence constructions do not require `E` to be a number field. That
hypothesis is required for the final finiteness theorem.

Write `U = (𝓞 E)ˣ` for the actual ring-integer unit group and
`T = NumberField.Units.torsion E` for its torsion subgroup. The quotient is
the existing group `U ⧸ T`, with the arithmetic action constructed in
`FullLogQuotientAction`. All representations are over the existing lifted
integer scalar ring `k = NormalizedTwoCocycle.CoefficientScalars.{v}` and
use the additive type tag on their multiplicative carriers.

## Arithmetic actions and representations

The native unit action is obtained from the action of `G` on the ring of
integers using Mathlib's `Units.mulDistribMulActionRight`, installed locally.
It applies the arithmetic automorphism to a unit and its inverse.
`unit_smul_mem_torsion` proves preservation of `T` by applying the corresponding
multiplicative automorphism to an element of finite order.

`unitTorsionAut F E` restricts these actual automorphisms to `T`; its inverse
uses the inverse field automorphism. The identity and composition laws follow
from those of the arithmetic action. The lemma `unitTorsionAut_coe` states
that its underlying unit is precisely the original arithmetic translate.
`unitTorsionAction F E` packages this restriction as an explicitly named
multiplicative action, again installed only locally in this module.

`ringIntegerUnitsRepresentation F E` and `unitTorsionRepresentation F E`
apply the existing `NormalizedTwoCocycle.coefficientRepresentation` to `U`
and `T`. Their carriers are `Additive U` and `Additive T`. The two
`_apply` theorems identify their actions with the actual unit action and its
restriction, respectively. In particular no action is defined by transport
from a desired cohomological comparison, and the ordinary units here are
not the full multiplicative group `Eˣ`.

## Inclusion, projection and exactness

`unitTorsionInclusion F E` is the morphism of representations induced by the
subgroup inclusion `T → U`. `unitsModuloTorsionProjection F E` is the morphism
induced by the actual quotient map `U → U ⧸ T`. Their `_apply` formulas are

\[
i(\operatorname{ofMul}(t))=\operatorname{ofMul}(t\text{ viewed in }U),
\qquad
q(\operatorname{ofMul}(x))=\operatorname{ofMul}([x]).
\]

Integer linearity follows from preservation of multiplication and integer
powers; lifted scalars act by their underlying integers. Intertwining is
the defining restriction or quotient formula for the arithmetic actions.

`unitTorsionSequence F E` packages these maps as a short complex. Its
zero-composite proof uses `QuotientGroup.eq_one_iff`: every torsion unit
has trivial quotient class. `unitTorsionSequence_shortExact F E` proves

\[
0\longrightarrow \operatorname{Additive}(T)
\xrightarrow{i}\operatorname{Additive}(U)
\xrightarrow{q}\operatorname{Additive}(U/T)\longrightarrow0
\]

in the category of representations over `k`. The implemented proof uses
`repShortExact_of_values`. Injectivity is subtype extensionality. A unit
whose quotient class is the identity belongs to `T`, giving the required
kernel preimage. Every quotient class has a unit representative, giving
surjectivity. Thus categorical exactness, the left monomorphism and the
right epimorphism all come from the actual subgroup and quotient maps.

With `[NumberField E]`, `unitTorsionRepresentation_finite F E` proves that
the torsion representation's underlying carrier is finite. It reuses
Mathlib's proved finiteness of `NumberField.Units.torsion E` and the fact
that an additive type tag preserves finiteness.

## Provenance and scope

Milne, *Class Field Theory*, v4.03 (2020), Chapter VII, proof of Proposition
3.1, printed p.209 (PDF page 218), uses the equivariant logarithm on the
unit group, whose kernel consists of roots of unity, to compare units with
their logarithmic image. Specializing the place set to all infinite places
gives the ordinary-unit setting here. Mathlib's `Units.torsion` is the
finite-order subgroup of the actual units; its `rootsOfUnity_eq_torsion`
identifies it with the corresponding roots-of-unity subgroup for a number
field. The exact sequence and arithmetic representations in this module
are derived categorical adapters of that finite-kernel step.

Together with the separate `fullLogEmbeddingRepresentationIso`, this
sequence connects ordinary units to their actual logarithmic image. This
module proves neither a Herbrand quotient comparison nor cohomological
finiteness. Those conclusions require the separate cyclic cohomology
calculus. The parent idele-class quotient theorem remains a distinct goal.
