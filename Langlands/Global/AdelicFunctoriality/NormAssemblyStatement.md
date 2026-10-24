# Determinant compatibility and quotient descent

`NormAssembly` is a proposition definition stating two reductions between
the published arithmetic objects and obligations in `NormStatement.lean`.
This module contains only the two `Prop` definitions `IdeleClassNormDescent`
and `NormAssembly`; it does not prove either reduction.

The first conjunct is
`CompletedTensorComparison.{u, v} → PrincipalNormCompatibility.{u, v}`.
The premise is bijectivity of the actual canonical completed tensor maps
at every finite and infinite place, for all number fields in the two
independent universes. The conclusion is the exact equality of principal
adeles: the already constructed product of local determinant norms sends
the diagonal image of `x : L` to the diagonal image of `Algebra.norm K x`.
The conclusion includes zero and is equality in the full adele ring.

The second conjunct, `IdeleClassNormDescent`, is a separate implication
from `PrincipalNormCompatibility.{u, v}`. For every number field
`K : Type u`, number field `L : Type v`, and actual `Algebra K L`, it
asserts the existence of a unique continuous group homomorphism

    f : IdeleClassGroup (𝓞 L) L →ₜ* IdeleClassGroup (𝓞 K) K

satisfying `f([a]) = [ideleNorm a]` for every actual idele `a` of `L`.
Both quotients are Mathlib's quotients by the principal-idele subgroups,
with the quotient topology. The formula refers to the published
`ideleNorm`, constructed from the local determinant norms, and fixes the
map on every representative. Uniqueness is among continuous group
homomorphisms satisfying this formula. The homomorphism is existentially
quantified in the conclusion, not supplied as an assumption.

These are derived assembly obligations for the existing norm construction.
The determinant norm commutes with scalar extension and finite products;
transport through the canonical tensor decomposition gives the first
implication. For the second, the principal-adele formula gives the
principal-unit formula and preservation of principal subgroups.
The quotient universal property then gives descent, the quotient topology
gives continuity, and surjectivity of the quotient map gives uniqueness.
These sentences summarize the reduction proved in the separate modules
named below; this module contains only the proposition definitions.

Both reductions and their arithmetic premises are proved in separate
published modules. `Langlands.Global.AdelicFunctoriality.normAssembly` in
[NormAssemblyProof](NormAssemblyProof.md) proves exactly
`NormAssembly.{u, v}`. Its first component is
`principalNormCompatibility_of_completedTensorComparison` from
[NormReduction](NormReduction.md). Its second component is
`ideleClassNormDescent`, proved in the same module, whose type is
`IdeleClassNormDescent.{u, v}` and whose witness is
`ideleClassNormOfPrincipalFormula` from
[NormDescentReduction](NormDescentReduction.md).
`Langlands.Global.AdelicFunctoriality.completedTensorComparison` in
[CompletedTensorComparisonProof](CompletedTensorComparisonProof.md) proves
the premise `CompletedTensorComparison.{u, v}` at every actual finite and
infinite place.
`Langlands.Global.AdelicFunctoriality.normCompatibility` in
[NormCompatibilityProof](NormCompatibilityProof.md) applies the first
component of `normAssembly` to that theorem. It thereby proves the combined
target `NormCompatibility.{u, v}`, whose second conjunct is
`PrincipalNormCompatibility.{u, v}`.

[IdeleClassNorm](IdeleClassNorm.md) constructs the actual continuous
quotient norm `Langlands.Global.AdelicFunctoriality.ideleClassNorm` for
number fields `K : Type u` and `L : Type v` with `Algebra K L`, without an
additional arithmetic hypothesis. It applies the first component of
`normAssembly` to `completedTensorComparison` to obtain the principal-adele
identity `adeleNorm_principal`, then instantiates
`ideleClassNormOfPrincipalFormula` with it. That module proves the
principal laws `ideleNorm_principal`, `ideleNorm_principal_le` and
`ideleClassNorm_principal`, the representative formula
`ideleClassNorm_mk`, continuity `continuous_ideleClassNorm`, and
uniqueness `ideleClassNorm_unique` among continuous homomorphisms with
that representative formula.

These later results do not change the present definitions.
`IdeleClassNormDescent` still has the explicit premise
`PrincipalNormCompatibility.{u, v}`, and `NormAssembly` is still a
conjunction of two implications. This module alone asserts no
unconditional norm on idele classes, proves neither of its targets, and
does not assert `NormCompatibility`. The proved norm results add no Galois
or abelian hypothesis. They do not prove global reciprocity or any other
class-field-theory statement, nor any local Langlands or automorphic
existence statement.

The arithmetic provenance is Andre Weil, *Basic Number Theory*, second
edition (1973), Chapter III section 3, printed pp. 53-54 (PDF pp. 70-71),
for the determinant norm and its behavior under base change and products;
Chapter III section 4, Theorem 4 and Corollary 3, printed pp. 56-58
(PDF pp. 73-75), for completed tensor decomposition and the norm formula;
Chapter IV section 1, Corollary 3, printed p. 64 (PDF p. 81), for the adelic
product; and Chapter IV sections 3-4, printed pp. 71-76 (PDF pp. 88-93),
for the idele topology (Definition 2, p. 71), the discrete subgroup of
principal ideles (p. 71), the regular norm as a morphism of idele groups
(corollary of Proposition 3, p. 74), and the quotient by the principal
ideles (Theorem 6, p. 76).
These original passages were read. Registered original:
`weil-1973-basic-number-theory`, SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
The separation into two implications is an internal organization of these
arguments around the published Mathlib-based project interfaces, rather
than a claim that Weil states this exact conjunction.
