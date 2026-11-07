# Base change of actual split-torus representation projectors

For commutative rings `R` and `A` in the same arbitrary universe and a ring map
`f : R →+* A`, this unit proves base-change compatibility for the actual
coefficient projectors of `RingRepresentationWeights`. Fix an actual group
scheme `G` over `Spec R`, an actual matrix representation `ρ` on `Fin N`, a finite
coordinate index type `I`, and an actual morphism `j : splitTorus (Spec R) I ⟶ G`.
No faithfulness, reductivity or nontriviality is needed for the coefficient
comparison. The dimension and rank may be zero.

Put `b = Spec.map f`. The map `splitTorus.baseChangeHomAlong I b j` is the composite
of the inverse canonical split-torus base-change isomorphism with the actual
base change of `j`. The representation over `A` is the actual representation
`ρ.baseChange b`, using the canonical general linear group base-change
isomorphism. In the namespace `SplitTorusRepresentationWeights`,
`universalMatrix_baseChange` identifies its universal matrix with the entrywise
image of the old matrix under the coefficient map `R[ℤ^I] → A[ℤ^I]`.
Taking coefficients gives `weight_baseChange`: for every integral exponent `m`,
the new weight matrix is exactly `(weight ρ I j m).map f`.

The proof first establishes
`MatrixRepresentation.affineMatrix_baseChange_map`. It allows any map between
affine test schemes over a base change whose underlying map is the spectrum of
the supplied test-ring map and whose actual points correspond under the
pullback adjunction. The existing point-matrix base-change formula and
naturality identify the matrices over global sections. The affine-section
comparison is the inverse of `Scheme.ΓSpecIso`; its naturality and cancellation
give the stated entrywise comparison over the test rings themselves.

For the universal points, `splitTorus.universalBaseChangeMap` is the spectrum
of the group-algebra coefficient map, considered over `Spec R`. Its structural
triangle follows by applying that map to scalar monomials. The inverse
canonical split-torus base-change identification preserves unit coordinates,
and restriction along this test-scheme map applies the coefficient map to each
coordinate monomial. These two coordinate formulas give
`splitTorus.universalPoint_baseChange`. Composing with `j` supplies exactly the
point correspondence required by the affine matrix lemma; taking monomial
coefficients finishes the projector comparison.

If `R` is a commutative local ring and `A` is nontrivial, the already constructed
projectors are idempotent, so `LocalIdempotentMatrix` detects whether each
coefficient matrix is zero after applying `f`. Thus
`weight_baseChange_ne_zero_iff` identifies the occurring exponents,
`weightSupport_baseChange` equates the exact finite supports, and
`weights_baseChange_eq` equates the corresponding sets. The definition
`weightSupportBaseChangeEquiv` gives an equivalence between the subtype of
occurring exponents over `R` and the subtype over `A`; its forward and inverse
maps preserve the entire integral coordinate vector, as recorded by the two
`simp` formulas. The ring map need not be injective, flat or local. These
statements therefore compare the supports on any two nontrivial fibres of the
same representation over a local base.

The construction is an internal consequence of the published point-coordinate,
pullback and affine-section APIs, the ring-valued projector identities, and
idempotent zero detection. It invokes no external structural theorem. It does
not construct an integral faithful representation, establish root-data
existence or reflection stability, or prove the host strict-Henselian
isomorphism statement.
