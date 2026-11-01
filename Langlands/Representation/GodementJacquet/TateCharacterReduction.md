# Actual character models for admissible irreducible GL₁ representations

Worker 458 proves `Langlands.GodementJacquet.exists_tateCharacterModel` and
constructs `tateCharacterModel` by classical choice from that theorem. For any field
`F : Type uF` with a topology making its actual `GeneralLinear 1 F` a
topological group, any complex module `V : Type uV`, and any admissible
irreducible representation `σ` on `V`, the construction returns a continuous
quasicharacter `χ` of `Fˣ` and an actual representation equivalence
`σ.Equiv (RankinSelberg.rankOneCharacter χ)`. The field and carrier universes
remain independent. No topology on `V` is assumed.

The published `admissibleSchur_centralCharacter` produces a locally constant
character `c` of the center acting by scalar multiplication. Composing it with
`GeneralLinear.scalarToCenter` gives `χ`. Its continuity follows from local
constancy of `c` and continuity of the scalar-matrix map into the center.
For every matrix `g` in GL₁, the published
`RankinSelberg.scalar_determinant_rankOne` identifies `g` with the scalar
matrix of its determinant. Consequently `σ g` acts on every vector by
`χ (determinant g)`.

Irreducibility gives a nonzero vector `v`. Its complex span is a
subrepresentation by the scalar action, and irreducibility makes this
nonzero subrepresentation the whole representation. The linear equivalence
from the complex scalars to the span of `v`, followed by its identification
with `V`, gives a linear equivalence `V ≃ₗ[ℂ] ℂ`. Scalar action shows directly
that this equivalence intertwines the two representations.

This is an internal derivation from the published admissible Schur theorem,
the published rank-one scalar-matrix identity, and Mathlib's actual
subrepresentations and linear equivalences. It establishes the representation
reduction required by the Tate matrix base proof. It assumes no Whittaker
certificate, chosen central character, finite dimension of the whole carrier,
or character-model equivalence. It makes no convergence, continuation,
normalized-generator, or functional-equation assertion.
