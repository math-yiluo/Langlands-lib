# The Weyl--inverse-transpose transform on Whittaker functions

Worker 31's construction uses Worker 16's unchanged actual matrix maps
from `Langlands.Group.GL.Maps`. The function formula is
`W̃(g) = W(wₙ (g⁻¹)ᵀ)`, with the all-ones anti-diagonal representative and
left multiplication by that representative.

The original formula and distinction between inverse-transpose pullback and
contragredient are JPSS, *Rankin–Selberg Convolutions* (1983), §2.1, printed
page 386, formula (4) and the following paragraph. That page was visually read.
Source `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The source identifies the pullback with the contragredient for irreducible
representations; this development does not assume that theorem.

The proof constructs the reflected unipotent matrix
`wₙ (u⁻¹)ᵀ wₙ`. Its lower entries vanish, and its diagonal entries are one.
Its adjacent upper entries are those of `u` in reversed order and negated.
Reindexing the finite sum proves reversal of the standard character.
Precomposition with the geometry owner's involution is linear and involutive
on actual functions. The left-unipotent transformation formula restricts it
to a linear equivalence between the standard- and inverse-character function
spaces. Right translation is transported through the actual inverse-transpose
automorphism.

For a representation `π` and a standard-character functional `ℓ`,
`inverseTransposePullback π` is the actual representation
`g ↦ π((g⁻¹)ᵀ)`. The functional `dualFunctional ψ π ℓ` sends `v` to
`ℓ(π(wₙ)v)`. The reflected-unipotent identity proves its inverse-character
equivariance, and `wₙ² = 1` proves that it remains nonzero when `ℓ` is nonzero.
The equality `dualFunction_coefficient` identifies the transformed coefficient
of `v` with the coefficient of this constructed representation and functional.

`dualModelLinearMap` restricts the function transform to the actual coefficient
images. Injectivity follows from the function-space equivalence; surjectivity
uses the same vector that witnesses membership in the target coefficient image.
`dualModelIntertwiner` proves compatibility with the inverse-transpose pullback
of the source action and the ordinary right-translation action of the target.
Its bijectivity supplies `dualModelEquiv`, a representation equivalence between
these two constructed coefficient models.

Smoothness of the pullback is the published theorem `Langlands.isSmooth_comp`
(Worker 0's continuous-pullback proof in
`Langlands.Representation.Smooth.Transfer.PullbackProof`), applied to the
geometry owner's continuous inverse-transpose homomorphism; the named lemma
`inverseTransposePullback_isSmooth` only specializes it.
`dualModel_isSmooth` then applies the existing theorem that an actual coefficient
image of a smooth representation is smooth. No topology is imposed on the
representation space, and these constructions require no irreducibility,
admissibility, finite-dimensionality, multiplicity-one theorem, or existence
of a nonzero functional.

The field and representation space have independent universes `uF` and `uV`.
The algebraic matrix identities work over a commutative ring. The character
uses the shared `UnitaryAdditiveCharacter` with complex values, and `V` is an
additive commutative group with a complex module structure. The function-space
equivalence is stated for a topological ring, using the geometry owner's
homeomorphism. The smoothness proof needs only the declared topology and the
owner's continuity theorem. The ranks are `n + 1` for every natural `n`,
including rank one, where the adjacent-entry sum is empty.

This is a derived construction implementing JPSS's explicit formula.
It does not prove the source's separate identification with the smooth
contragredient, nor a functional equation or an epsilon or gamma factor.
The concrete-character construction is supplied in the companion
`Langlands.Representation.Whittaker.GeneralLinear` pair in this contribution.
`Langlands.Group.GL.Maps`, `Langlands.Representation.Smooth.Transfer.PullbackProof`
and the companion's geometry, harmonic-analysis, matrix-coefficient and
algebraic-model imports are published Library modules. Their published Lean
sources match the sources used for native compilation. No geometry
implementation is duplicated in this pair.

The complete module compiled with the project's pinned Lean environment,
without diagnostics. This native check is development evidence; independent
semantic review and current Library publication are still required.
