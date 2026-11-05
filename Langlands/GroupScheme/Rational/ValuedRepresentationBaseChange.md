# Actual representation scalar extension and coefficient integrality

This derived unit supplies a scalar-extension step in the proof of
Kaletha–Prasad, Lemma 2.2.11. Its primary construction,
`Langlands.GroupScheme.MatrixRepresentation.baseChange`, sends an actual
representation `ρ : G → GL_n` over `Spec R` and an actual scheme morphism
`b : Spec R' → Spec R` to the composite of the base-changed representation
with the published canonical isomorphism `(GL_n)_R' ≅ GL_n` over `R'`.
Thus its output is an actual representation of the actual base-changed
group scheme.

`pointMatrix_baseChange` identifies its matrix on every relative test scheme
with the original matrix through the published pullback-adjunction point
equivalence. This uses the point formula for the general linear base-change
isomorphism and naturality of the base-change point equivalence with
respect to group-scheme homomorphisms.

For any field extension `K/F`,
`baseChangePointsEquiv_geometricRationalPoint` identifies the actual
scalar extension of a ground-field point with its constant point over `K`
under that equivalence. The proof compares their underlying scheme
morphisms using the first projection of the pullback.
`rationalMatrix_baseChange_geometricRationalPoint` then identifies the
base-changed representation's actual rational matrix with the entrywise
image of `ρ.rationalMatrix g` under `algebraMap F K`. The implemented
proof uses the preceding point formula, the constant-point matrix formula,
and the canonical global-section isomorphism `Γ(Spec K, O) ≅ K`.

If the two fields have compatible valuative relations, the theorem
`charpoly_coeff_baseChange_geometricRationalPoint_vle_one_iff` preserves
and reflects each characteristic-coefficient inequality `≤ᵥ 1` at every
such actual point. It rewrites the rational matrix, uses naturality of
the characteristic polynomial and its coefficients under a ring map,
and applies `ValuativeExtension.vle_iff_vle`.
`HasIntegralCharacteristicPolynomials.baseChange_image` applies that
equivalence to the image of all actual ground-field rational points.
It does not assert coefficient integrality at arbitrary `K`-points.

The base-ring universe is arbitrary. The matrix index type in the
construction and matrix comparison is any finite small type; the spectral
specialization uses `Fin N`, including `N = 0`. The coefficient results
require compatibility of the valued extension explicitly. They do not
require algebraicity, a topology, a local-field structure, reductivity,
faithfulness, density, or semisimplicity. They assert neither boundedness
of the extended image nor the host `ReductiveSpectralBoundednessStatement`.

The original proof passes to invariant subspaces over an algebraic closure
and uses integrality of the original matrices on those scalar-extended
points. This unit derives the actual representation and coefficient
comparison needed for that passage from the published scheme-theoretic
base change and matrix APIs; it is not a separate assertion quoted
verbatim from the book.

Sources: Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Lemma 2.2.11 and its composition-factor argument, printed pp.72–73 /
PDF pp.103–104; registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The November 2024 corrections, Section 2.2, PDF p.24, impose Henselianity
throughout the section and amend the extension-topology assertion of
Lemma 2.2.5. This unit uses only functoriality and explicit valuative
compatibility, so it does not invoke that topology comparison or
Henselianity. Registered corrections source
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
