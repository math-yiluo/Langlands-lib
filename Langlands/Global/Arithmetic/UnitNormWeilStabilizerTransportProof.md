# Unit-norm to Weil stabilizer transport: proof

Author: Worker 84.

The theorem `Langlands.Global.unitNormWeilStabilizerTransport.{u}` proves
`Langlands.Global.UnitNormWeilStabilizerTransportStatement.{u}`.
The proof retains every prime, the arbitrary carrier universe, the given
normalized reciprocity family and the given continuous field character.
It introduces no additional existence or finite-order assumption.

## Reciprocity and the two field presentations

Use the statement's notation `M`, `h`, `L`, `a` and `χL`.
For a Weil element `x` in `W_M`, the norm relation in the supplied normalized
reciprocity system gives

\[
 \operatorname{rec}_E(x)
   = N_{M/E}(\operatorname{rec}_M(x)).
\]

The helper `reciprocityUnits_norm` evaluates that equality of homomorphisms
at the actual image of `x` in the abelianization. Composing with `χ` gives
the formula for the closure restriction used in the final proof.

The map `reciprocityUnits F e M` is surjective: the abelianization
projection is the genuine surjective quotient map, and `e M` is an
equivalence. `reciprocityUnits_surjective` takes a representative of
`(e M).symm z`. No density argument is used.

For `w` in the local Weil group, let `s` be its projection to the absolute
Galois group. The conjugation reciprocity square initially lands in
`M.conj s`. Normality makes its underlying intermediate field equal to
`M.field`. The helper `reciprocityUnits_field_eq` handles this dependent
change of field by comparing values inside the algebraic closure.
`reciprocityUnits_conj_normal` combines that comparison with the square
and `AlgEquiv.restrictNormal_commutes` to obtain

\[
 \operatorname{rec}_M(w x w^{-1})
   = (s|_M)(\operatorname{rec}_M(x)).
\]

This equation uses the actual automorphism on units.

The helper `unitsNorm_restrict` identifies the inclusion norm
`E.unitsNorm M h` with the norm to `L` after applying `a`.
It installs the inclusion algebra and its finite-dimensional structure,
then applies `Algebra.norm_eq_of_ringEquiv` to
`IntermediateField.restrictAlgEquiv h`. The compatibility of the two
embeddings is checked elementwise. Consequently
`normCharacter_restrict` proves, for each unit `z` of `M.field`,

\[
 \chi_L(N_{M/L}(z))=\chi(N_{M/E}(z)).
\]

This is an equality through the canonical equivalence, not an
identification of the two field types or their topologies.

## From Weil invariance to the fixing subgroup

Suppose `g` fixes the closure restriction under inverse conjugation.
Set `σ := projection(g⁻¹)|_M`. Surjectivity of `reciprocityUnits F e M`,
the norm formula and the normal conjugation formula show

\[
 \chi_L(N_{M/L}(\sigma z))=\chi_L(N_{M/L}(z))
\]

for every unit `z` of `M.field`. Restricting this equality to units of
canonical norm one permits application of the supplied exact
unit-stabilizer condition. Thus `σ` fixes `L`.

The helper `restrictNormal_mem_fixing_iff` compares pointwise fixing of
`L` with pointwise fixing of `E.field` in the common closure. In one
direction it sends an element of `E.field` to `L` by
`restrictAlgEquiv h`, takes its fixing equation in `M.field`, and embeds
the equation in the closure. In the other direction it uses
`IntermediateField.mem_restrict` and `AlgEquiv.restrictNormal_apply`.
Hence `projection(g⁻¹)` fixes `E.field`, which means `g⁻¹ ∈ W_E`.
Closure under inversion gives `g ∈ W_E`.

## The reverse implication

If `g ∈ W_E`, conjugation by `g⁻¹` is inner in `W_E`.
`closureRestriction_inner` writes the argument after subgroup inclusion
as `gE⁻¹ * xE * gE`. A character into the commutative group `ℂˣ` takes
this to its value at `xE`, by multiplicativity, inversion and cancellation.
This proves the reverse implication directly. It needs no independent
norm-invariance premise.

The final theorem assembles these implications for the actual normal
closure. The canonical norm is used only to specialize the forward
invariance equality to the supplied unit-stabilizer hypothesis.

## Dependencies and source relationship

The proof imports its target module and `Mathlib.RingTheory.Norm.Basic`.
All project constructions and reciprocity squares come from the target's
unchanged Library imports. The extra Mathlib import supplies the
ring-equivalence norm comparison.

The motivating source is Harris 1998, proof of Lemma 4.7, printed
pp.204–206 / one-based PDF pp.28–30, especially (4.12) on p.204:
source `harris-1998-local-langlands`, SHA256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
This is a proof of the derived comparison of existing Library conventions.
It does not implement Harris's character-existence argument, his
Clifford–Mackey step, or a characteristic-two repair.

Reciprocity surjectivity is reused from `LocalFactor.CommonClosure.reciprocityUnits_surjective`.
