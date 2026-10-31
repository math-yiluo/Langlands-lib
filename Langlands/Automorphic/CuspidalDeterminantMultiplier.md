# Determinant multiplication and actual cuspidal functions

Author: Worker 2.

This internal construction reuses `Langlands.Automorphic.DeterminantMultiplier`,
the actual standard block-unipotent matrices from `Langlands.Group.GL.BlockUnipotent`
and the maximal-block constant terms and cuspidal subrepresentation from
`Langlands.Automorphic.ConstantTerm`. The number field is `F : Type u`, every
natural rank is allowed, and all function coefficients are complex.

`Langlands.GeneralLinear.determinant_blockUnipotent` proves determinant one for
`blockUnipotent h X` over any commutative ring, including empty blocks. The
implemented proof passes to underlying matrices, removes the common row and
column reindexing, and uses the determinant of an upper block-triangular matrix.
Both diagonal blocks are identities. The pulled-back Hecke determinant character
therefore takes value one on every such actual adelic unipotent.

Consequently the constant-term integrand satisfies
`(Mχ f)(u(X̃) g) = χ(det g) f(u(X̃) g)` for the existing chosen lift `X̃`.
`constantTerm_determinantMultiplier` pulls that scalar out of the actual Bochner
integral against `matrixQuotientHaar F a b`. It retains the existing Borel
sigma-algebra and Haar probability normalization, for every split `a + b = n`.
The integrand identity needs no compactness hypothesis. Constant terms and all
following cuspidal declarations retain `[CompactSpace (AdeleQuotient F)]`, which
can be supplied by the separately published `compactSpace_adeleQuotient` proof.
No additional measure, topology or integrability assumption is introduced.

`IsCuspidal.determinantMultiplier` proves cuspidality is preserved for every
actual continuous Hecke character, with no finite-order or unitarity restriction.
The converse follows by applying the inverse multiplier. The vanishing condition
is the existing one for every positive maximal-block split and every group point;
zero and rank-one cases use that same definition.

`CuspidalContinuousFunctions` abbreviates exactly the existing
`cuspidalSubrepresentation` carrier and inherits its subtype topology.
`CuspidalContinuousFunctions.determinantMultiplier` uses Mathlib's
`ContinuousLinearEquiv.ofSubmodules` to restrict the constructed ambient
automorphism to this submodule. Its image equality is proved using cuspidality
preservation and the actual inverse multiplier. The evaluation formulas give
multiplication by `χ(det g)` and its inverse; the restricted right action obeys
`R(g) Mχ = χ(det g) Mχ R(g)`. The three named local additive groups are the
canonical submodule structures.

The provenance is the direct calculation from those existing constructions and
Mathlib's determinant and integral identities. This module does not claim a new
external-source comparison, preservation of the analytic automorphic conditions,
or a total determinant twist of operator realizations or their classes.
