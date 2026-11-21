# Properness of supplied dynamic parabolic quotients

`Langlands.GroupScheme.dynamicQuotientProper` proves
`Langlands.GroupScheme.DynamicQuotientProperStatement.{u}` for every universe
`u`. It applies to any connected reductive group scheme `G` over an
algebraically closed field of any characteristic and any cocharacter `χ`,
including trivial and central cocharacters. The supplied quotient `q : G.X → Q`
has separated, locally finite type and quasi-compact structure morphism.
Its projection is smooth, surjective and quasi-compact and satisfies the
exact right-coset fiber condition for `Dynamic.parabolic χ` on every relative
scheme test, including nonreduced and nonaffine schemes. The conclusion is
`IsProper Q.hom` for this `Q`.
[Published statement](QuotientProperStatement.md)

The proof supplies `reductiveLinearQuotientAffine` to
`dynamicQuotientProper_of_reductiveLinearQuotientAffine`. The affineness
theorem uses geometric reductivity from the independently proved rank-one
central cover. It constructs affine principal opens on the supplied
homogeneous quotient and proves that their defining sections generate the
unit ideal in its global section ring.
[Affineness proof](../Reductive/LinearQuotientAffineProof.md)
[Geometric reductivity proof](../Reductive/IndependentGeometricReductivityProof.md)

The properness reduction chooses a closed representation of `G` into a
general linear group. In the resulting affine homogeneous quotient by `G`,
the orbit of the identity coset under the ambient dynamic parabolic is
closed. Pullback and inversion give closedness of the corresponding
subgroup product. The original supplied `Q` then maps by a closed immersion
to the proper dynamic quotient of the general linear group, whose
properness follows from matrix diagonalization and the standard
upper-triangular subgroup. Composing that closed immersion with the proper
structure morphism gives properness of `Q.hom`.
[Properness reduction](QuotientProperAffineReduction.md)
[General linear quotient](GeneralLinearQuotientProper.md)

The type-and-value audit of `dynamicQuotientProper` followed 129,382
constants, including 33,280 project Library dependencies. It found zero
matches for the five excluded statements, their proofs, and the watched
regular-cocharacter and Borel proof steps. The older geometric-reductivity
proof reached `regularCocharacterBorel` in the control check. The proof is
an internal composition of the published affineness theorem and properness
reduction.
[Dependency audit method](../../../notes/group-schemes/haboush-independence-audit.md)
