# The cone offset of a tempered unramified full piece

This is a derived formulation of the first cone step in Renard,
*Représentations des groupes réductifs p-adiques*, 2026 edition, VII.4.1,
printed pp.241–242 / PDF pp.247–248, especially (VII.4.1.1) and the final
addition of real parts. It applies to supplied actual geometric-lemma
intersection data for any two rational parabolics. In the opposite case,
Renard's target cone is the cone for the opposite parabolic.

The field universe `u` and representation-carrier universe `v` are independent.
The ambient group has the canonical rational-point topology, is affine and
smooth and locally of finite type, and its points satisfy the explicit local
compactness and nonarchimedean hypotheses. All parabolic, Levi, radical and
multiplication data are the original data of `GeometricLemmaIntersectionDatum`.

## The actual twist parameter

Let `D` be intersection data for `P z Q`, let `a : A → L` be the target Levi's
split component, and let `a' : A' → D.L'` be a split component of the target
intersection Levi. The given map `f : A → A'` must satisfy

`groupHom f ≫ a' ≫ D.lQ' ≫ D.q' = a`.

`D.unramifiedPieceRealPart ha a' f ψ` is defined as the normalized real part of
the original unramified character `ψ` of the source Levi `M`, pulled back
through the composite

`groupHom f ≫ a' ≫ D.φ.hom ≫ D.l' ≫ D.p' : A → M`.

This is a definition using the actual intersection morphisms. It does not
identify this parameter with a Weyl translate or assume such an identification.

## Cone offset and exclusion

Suppose that `σ` is normalized-exponent tempered and that the normalized source
Jacquet module of `τ = σ ⊗ ψ` in `D` is admissible. Let `presQ` be any root
presentation of the target parabolic and component, with ambient relative roots
closed under negation. For every generalized eigencharacter `χ` of the full
piece `D.pieceFunctor.obj τ`, restricted to `A(F)`, the theorem
`exists_normalizedRealPart_eq_cone_add_unramifiedPieceRealPart` produces
`x ∈ presQ.nonnegCone` with

`normalizedRealPart χ = x + D.unramifiedPieceRealPart ha a' f ψ`.

The next theorem states the equivalent difference membership. The last theorem
excludes any test parameter `paramA` whenever

`D.unramifiedPieceRealPart ha a' f ψ - paramA`

is a nonzero vector of the same target cone. This is a conditional exclusion
criterion; the displacement premise is explicit.

## Implemented proof and remaining obligations

The proof first applies the published exact full-piece untwisting theorem to
obtain an untwisted source Jacquet exponent `θ`. Temperedness puts its normalized
real part in the source parabolic cone. The smooth exponent's open kernel permits
normalized real-part functoriality along `f`.
`D.restrictReal_mem_nonnegCone` then transfers this real part into the target
cone. The published additive real-part identity gives the displayed sum.
For exclusion, adding a cone vector to a nonzero cone vector cannot give zero,
by the target presentation's strictly positive defining evaluation.

Source Jacquet admissibility remains an explicit premise. The results use the
full piece, including its target normalized induction, and do not assume the
represented geometric lemma's filtration. They do not establish admissibility,
actual Weyl-parameter transport, identification of the opposite cone, a
double-coset comparison, full Langlands-triplet spectral separation,
`LanglandsTripletOppositeRegularityStatement`, or the dimension-one conclusion.
