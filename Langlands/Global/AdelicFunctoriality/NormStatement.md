# Local/global compatibility for actual adelic norms

`NormCompatibility` is an exact proposition definition, not a theorem. It
conjoins two arithmetic obligations for arbitrary number fields `K : Type u`
and `L : Type v`, with their field, number-field and `Algebra K L` instances.
The universes are independent. Finite dimensionality follows from the
number-field hypotheses; it is not an added assumption.

`CompletedTensorComparison` asserts that the maps already constructed in
`Norm.lean` are bijective. At a finite place `p`, the map is

    K_p ⊗[K] L → ∏ (q above p), L_q,
    x ⊗ y ↦ (completionMap(p,q)(x) · y)_q.

The index is the actual subtype of height-one primes of the ring of integers
of `L` satisfying the lies-over relation. At an infinite place it is the
actual subtype of Mathlib infinite places above that place, with Mathlib's
completion embedding. The maps, scalar towers and tensor formulas are
constructed; the statement does not quantify over a proposed equivalence,
assume a decomposition theorem, or assume the desired norm identity.

`PrincipalNormCompatibility` asserts equality in the actual full adele ring
of `K`, for every `x : L`, including zero. Its left side applies the
constructed adelic norm to the diagonal adele of `x`. Its right side is the
diagonal image of `Algebra.norm K x`. Thus the statement fixes the precise
normalization and direction of the arithmetic norm. It is not an equality
only of absolute values or valuations, and it is not an extension-of-scalars
embedding. The already implemented norm is multiplicative and continuous;
this statement supplies the additional local/global arithmetic identity.

The tensor comparison and principal identity are separate conjuncts whose
proofs are now published. `Norm.lean` proves the infinite-place comparison
from weak approximation and Mathlib's infinite local-degree sum.
`Langlands.Global.AdelicFunctoriality.completedTensorComparison` in
[CompletedTensorComparisonProof](CompletedTensorComparisonProof.md) proves
both the finite and infinite comparisons, using the proved completed
local-degree bounds for the finite part.

[NormReduction](NormReduction.md) implements the determinant argument:
`Langlands.Global.AdelicFunctoriality.norm_baseChange` proves compatibility
with scalar extension, while
`Langlands.Global.AdelicFunctoriality.norm_prod` and
`Langlands.Global.AdelicFunctoriality.norm_pi` prove the binary and finite
dependent-product formulas. The theorem
`Langlands.Global.AdelicFunctoriality.principalNormCompatibility_of_completedTensorComparison`
derives the principal identity from the comparison target.
`Langlands.Global.AdelicFunctoriality.normCompatibility` in
[NormCompatibilityProof](NormCompatibilityProof.md) supplies the proved
comparison to this reduction through `normAssembly`, proving the entire
`Langlands.Global.AdelicFunctoriality.NormCompatibility.{u, v}` target
without an additional arithmetic premise.

[IdeleClassNorm](IdeleClassNorm.md) proves the principal-adele and
principal-idele identities and preservation of the principal subgroup,
then constructs `Langlands.Global.AdelicFunctoriality.ideleClassNorm`.
Its representative formula, continuity, principal-class identity and
uniqueness are proved there. The present file still only defines `Prop`
targets and imports `Norm`; it does not itself assert quotient-norm
existence. These results require no Galois or abelian hypothesis and do
not prove the separate class-field-theory statements.

The original source is Andre Weil, *Basic Number Theory*, second edition
(1973), Chapter III section 4, Theorem 4, printed pp. 56-57 (PDF pp. 73-74),
and Corollary 3, printed p. 58 (PDF p. 75). The adelic product formula is
Chapter IV section 1, Corollary 3, printed p. 64 (PDF p. 81). The determinant
definition of the norm and its behavior under algebra isomorphism and
products are in Chapter III section 3, printed pp. 53-54 (PDF pp. 70-71).
Registered original: `weil-1973-basic-number-theory`, SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
These original pages were read. The precise displayed formulas are their
realization on the pinned Mathlib completions and the constructed adelic map.
