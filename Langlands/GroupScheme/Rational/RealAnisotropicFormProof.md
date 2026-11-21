# The anisotropic form of a real semisimple group

Author Worker 263.

`Langlands.GroupScheme.realAnisotropicForm` proves the published
`Langlands.GroupScheme.RealAnisotropicFormStatement`, the group-scheme
formulation of Milne's *Algebraic Groups* (2017), Theorem 25.56, p. 561.
The statement records the comparison with Milne's conventions for forms and
anisotropy. [Statement and source](RealAnisotropicFormStatement.md)

The proof applies `realAnisotropicForm_of_compactFormInputs`, supplying
`realCompactFormExistence` and `realCompactFormUniqueness` directly. For the
third input, connected reductivity supplies the affine instances for `G`.
The compactness conjunct of `realAnisotropicCompactConnected` makes
`RingPoint ℝ G.X ℝ` a compact space. The inverse of
`affinePointsRingPointHomeomorph` transports compactness to the affine
coefficient points with their regular-evaluation topology. Compactness of the
whole space then gives `HasCompactRealPoints G`.
[Real-point compactness](RealAnisotropicCompactConnectedProof.md)
[Point comparison](../AffinePointRingPointComparison.md)

The reduction applies compact-form existence to the complexification, which is
semisimple by `isSemisimpleFieldExtension`. The resulting real semisimple form
is anisotropic by `isAnisotropic_of_hasCompactRealPoints`. For uniqueness, the
reduction obtains compactness for each anisotropic form and composes their
given isomorphisms over ℂ to compare their complexifications.
`realCompactFormUniqueness` then gives an isomorphism over ℝ.
[Reduction](RealAnisotropicFormCompactReduction.md)
[Existence](RealCompactFormExistenceProof.md)
[Uniqueness](RealCompactFormUniquenessProof.md)
