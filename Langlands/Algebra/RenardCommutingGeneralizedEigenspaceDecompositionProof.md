# Renard C.I: proof of the actual joint decomposition

`Langlands.Renard.commutingGeneralizedEigenspaceDecomposition.{u}` proves
exactly the unchanged published proposition
`Langlands.Renard.CommutingGeneralizedEigenspaceDecompositionStatement.{u}`.
It establishes all six conclusions for every finite-dimensional complex
module in arbitrary carrier universe, every natural tuple length, and every
pairwise commuting original tuple. The proof imports the published actual
joint-space construction and statement without changing either pair.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix C.I,
printed p.275 / one-based PDF281, first proof paragraph. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 308 reread PDF281–282 and verified that fingerprint while preparing
this proof. The source successively refines the characteristic spaces of
the original generators and obtains invariant direct summands. Their
actual intersections are the imported `CommutingReduction.jointSpace`.
Finite support and the dimension identity are finite-dimensional
consequences of that decomposition. The explicit faithfulness and
image-dimension assertions are derived linear algebra spelling out the
comparison needed to reduce the source's algebra to its block actions;
they are not separately displayed lemmas in the book.

The supplementary registered source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
Worker 308 reread PDF18–19 and checked that fingerprint. Its C.I entries
correct later numerical steps in the older edition; the 2026 original
governs the present decomposition.

## Implemented decomposition and dimensions

Write `R = NilpotentFiltration.generatedAlgebra a`, the actual unital
adjoin of the original tuple in `Module.End ℂ V`. For every complex tuple
`χ`, the submodule `jointSpace a χ` is precisely
`⨅ i, (a i).maxGenEigenspace (χ i)`. The supported index is exactly
`jointBlockIndex a = {χ // jointSpace a χ ≠ ⊥}`.

Commutation makes every original generator preserve the generalized
eigenspaces of every other generator. Applying Mathlib's
`Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo` therefore
gives independence of the full actual intersection family, including its
zero members. Algebraic closure of `ℂ`, imported through
`Mathlib.Analysis.Complex.Polynomial.Basic`, gives each generator's
spanning generalized-eigenspace family. Mathlib's
`Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`
then gives spanning by all the joint intersections.

The finite-dimensional support theorem
`iSupIndep.fintypeNeBotOfFiniteDimensional` produces a `Fintype` on the
actual nonzero subtype, proving its `Finite` assertion. Removing bottom
members leaves the same supremum: each full-family member is either bottom
or occurs in that supported subtype. This proves the required supported
spanning assertion.

For each separately quantified `Fintype` structure `F` on that same
subtype, the proof installs the supplied `F`. Independence restricts along
`Subtype.val_injective`, and `iSupIndep.linearEquiv` identifies the direct
sum of the supported original spaces with `V`. Its equality of finranks,
combined with `Module.finrank_directSum`, proves the exact requested
dimension sum. Thus the sum is proved for every supplied enumeration.

## Original actions and actual image dimensions

The faithfulness proof uses exactly the function in the statement,
`r ↦ (χ ↦ blockRestriction a hcomm χ.val r)`. If `r` and `s` have equal
restrictions, evaluating on any vector in an actual supported block and
including back into `V` gives `r(v) = s(v)`. This uses the defining
original-action equality of `blockRestriction` (also exported as
`blockRestriction_apply`). Each supported submodule is therefore contained
in the kernel of the difference of the original endomorphisms. Their
supremum is top, so that kernel contains all of `V`. Extensionality of
linear maps and of the original algebra subtype gives `r = s`.

For the last assertion, again for each supplied `Fintype` structure, the
proof applies the published
`Langlands.CommutingDimension.dimension_le_sum_restrictions` to `R` and
the supported actual joint spaces. Stability is the imported
`jointSpace_stable`, for every element of the original generated algebra.
The generic restriction homomorphism specializes definitionally to the
original `blockRestriction`; its range is the actual action image. The
published `blockAlgebra_eq_range` identifies each such image with
`blockAlgebra a hcomm χ.val`. Applying finrank to that equality and summing
proves precisely the dimension comparison with the actual block algebras.
No full block endomorphism algebra replaces an action image.

## Scope and attribution

The proof introduces no basis, externally supplied decomposition,
invertibility, or original nilpotence premise. Every eigenvalue is
allowed, including zero, and zero or repeated tuple entries require no
special cases. It retains the empty tuple: there is a unique eigenvalue
tuple, its intersection is top, and it is supported exactly for a nonzero
carrier. Its generated algebra is the scalar algebra under the unital
convention. On a zero carrier every joint space is bottom, the supported
index is empty, and both dimension sums are zero; the original algebra is
also zero-dimensional and its restriction function remains injective.
The generic lemmas used in the proof include these boundary cases. Scalars
and the identity consume no tuple entry.

Worker 308 implemented this extraction. The independence, supported
spanning, direct-sum dimension and kernel arguments adapt Worker 307's
published `Langlands.Algebra.CommutingDimensionPrimary`, which also
supplies the imported range-dimension helper. Worker 709 supplied the
actual-block target's source correspondence and the extraction plan used
here. Both are credited as coauthors. The published actual-block
construction, credited there to Workers 709, 307 and 1044, is imported
unchanged.

This proof establishes the joint-decomposition and original-restriction
intermediate result. The later comparison by real powers, the actual-block
nilpotent-maximum reduction, the floor recurrence and the maximum bound
remain separate units. The proof does not invoke the known final commuting
dimension theorem to replace any of the six assertions.
