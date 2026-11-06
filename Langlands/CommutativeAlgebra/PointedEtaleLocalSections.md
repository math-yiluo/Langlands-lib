# Pointed etale specialization of smooth algebras

Author: Worker 1683.

This module is `Langlands.CommutativeAlgebra.PointedEtaleLocalSections`.
It imports the published unpointed algebraic local-section module
`Langlands.CommutativeAlgebra.EtaleLocalSections` and uses its
`exists_away_lift`. It supplies the algebraic input for the pointed refinement
of smooth local sections in
`Langlands.AlgebraicGeometry.SmoothPointedEtaleLocalSectionsStatement`.
All rings lie in an arbitrary universe `u`.

## Mathematical content

Let `R → S` be a smooth homomorphism of commutative rings, let `𝔭` be a prime
of `R`, and let `φ : S →ₐ[R] κ(𝔭)` be a specified rational point of the fibre.
`exists_etale_factor_of_smooth` constructs a commutative `R`-algebra `R'`
that is etale over `R`, maps `ψ : S →ₐ[R] R'` and
`ρ : R' →ₐ[R] κ(𝔭)`, and the exact equation `ρ.comp ψ = φ`.
The map `ρ` retains the original residue field. In particular, the
construction preserves the supplied point, including its map on elements,
and does not replace it by a point over a larger field.

The helper `exists_etale_factor_of_polynomial` proves the same factorization
when `S` is etale over `P = R[X₁, …, Xₙ]`, compatibly with its `R`-algebra
structure. Only finitely many polynomial variables are required; the
standard-etale hypothesis is not needed for this helper.

## Implemented proof

For the polynomial case, write `cᵢ` for the image under `φ` of the image in
`S` of `Xᵢ`. The published `exists_away_lift`, applied to the finite set of
these elements of `κ(𝔭)`, gives a localization `Rb = R[1/b]` and a ring
map `β : Rb → κ(𝔭)` extending `R → κ(𝔭)`, with lifts `aᵢ` of the `cᵢ`.
The element `b` avoids `𝔭`, although the proof subsequently needs only the
map and its lifting property.

Let `θ : P →ₐ[R] Rb` send `Xᵢ` to `aᵢ`. Equality on coefficients and
variables proves that `β ∘ θ` equals the restriction of `φ` to `P`.
Use this compatibility to regard both `β` and `φ` as `P`-algebra maps, and
set `R' = Rb ⊗[P] S`. Etaleness over `Rb` follows by base change of
`P → S`; etaleness over `R` follows by composition with the principal
localization. The map `ψ` is the tensor-product inclusion of `S`, restricted
to `R`-scalars. The tensor-product universal property supplies `ρ` from
`β` and `φ`. Evaluating it on `1 ⊗ x` proves the exact equation
`ρ.comp ψ = φ`.

For a smooth `S`, the kernel `𝔮` of `φ` is prime. Mathlib's
`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial` supplies
`g ∉ 𝔮` such that `S[1/g]` is standard etale over a polynomial algebra.
The value `φ(g)` is nonzero in the residue field, hence a unit, so `φ`
extends to `S[1/g]`. Apply the polynomial lemma to this extension, then
precompose its map `ψ` by `S → S[1/g]`. The two factorization equations
compose to the desired equation for the original `φ`.

## Provenance and scope

These are derived helper lemmas for the rational-point refinement described
in the statement's Markdown. The underlying geometric local-section source
is The Stacks Project, Lemma 37.38.6 (Tag 055U), registered as
`stacks-055U-smooth-etale-local-sections-2026-11-02`. The implemented proof
uses polynomial specialization and a tensor product in place of that
source's complete-intersection construction. Every algebraic lifting and
comparison is established here from published lemmas; no approximation
principle or extra field-extension hypothesis is assumed.
