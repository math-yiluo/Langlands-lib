# Existence of spectra for actual standard spherical Hecke operators

The theorem `Langlands.Unramified.sphericalHeckeSpectrumExistence` proves exactly
`Langlands.Unramified.SphericalHeckeSpectrumExistenceStatement.{uF,uV}`. For every
prime `p`, every `F : PadicField.{uF} p`, every positive rank `n = r+1`, and every
actual irreducible admissible smooth object `A` with nonzero spherical fixed
submodule, it constructs `s : Eigenvalues n` satisfying
`HasSphericalHeckeSpectrum F A s`.

The carrier universe `uV` is independent of `uF`. The proof uses the original
representation and fixed submodule, the canonical field and general-linear-group
topologies, the existing spherical subgroup, and its Haar measure of mass one.
All indices `i : Fin (r+2)`, including zero and the last index, occur in the
conclusion. The scalars used in the construction are derived from the actual
operators; they are not additional hypotheses or externally supplied data.

## Factorization with multiplicities

`Langlands.Unramified.Eigenvalues.exists_eulerPolynomial` states that a complex
polynomial `P` with `P.eval 0 = 1` is `eulerPolynomial s` for some
`s : Eigenvalues P.natDegree`. The hypothesis first implies `P ≠ 0` and that every
member of `P.roots` is nonzero. The proof maps the attached multiset of roots to
complex units by `a ↦ (Units.mk0 a ha)⁻¹`. Mathlib's algebraic-closedness result
`IsAlgClosed.card_roots_eq_natDegree` gives its cardinality. Using a multiset,
including its repeated members, retains all multiplicities.

For each root `a`, the proof rewrites

`X - C a = C (-a) * (1 - C (a⁻¹) * X)`.

The splitting identity `Polynomial.Splits.eq_prod_roots` therefore writes `P`
as a constant factor times the product of the desired Euler factors.
Evaluating that identity at zero identifies the constant factor as one.
This also covers the degree-zero polynomial `P = 1`.

## Invertibility of the central standard element

`Langlands.Unramified.standardHeckeElement_last_isUnit F r` proves that the last
standard element is a unit in the actual spherical Hecke algebra. Let
`z = standardDiagonal F r (Fin.last (r+1))`. The definition of the diagonal and
the bounds on its finite indices show that it is the scalar uniformizer matrix.
The proof checks its commutation with an arbitrary matrix entry by entry, so `z`
is central and hence normalizes the spherical subgroup. Its inverse also
normalizes that subgroup.

Writing `D(g)` for the existing normalized double-coset element, the published
`Hecke.HeckeAlgebra.Corner.doubleCoset_mul_mul_of_mem_normalizer`, applied with
middle argument `1`, gives both

`D(z) * D(z⁻¹) = 1` and `D(z⁻¹) * D(z) = 1`.

Here `D(1) = 1`, and `D(z)` is definitionally the last standard Hecke element.
These equations explicitly construct its unit structure. Workers 257 and 267
contributed the central-element dependency analysis and this inverse-double-coset
route. The proof uses the published double-coset operations directly; it has no
dependency on the spherical generation theorem.

## Assembly on the original fixed line

The published `sphericalFixedLine` gives complex dimension one for the original
nonzero fixed submodule `V`. Mathlib's
`LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one` then supplies, for every
standard index, a scalar `c_i` with `T_i = c_i • id` on `V`.
A nonzero vector of `V` and `standardHeckeOperator_zero` give `c_0 = 1`.
Mapping the unit structure of the last Hecke element through the actual corner
action shows that its operator is a unit in `Module.End ℂ V`. Since `V` is
nontrivial, this operator cannot be zero, and consequently `c_n ≠ 0`.

Let `Q = sqrt(residueCardinality)`, embedded from the real numbers into the
complex numbers. The existing strict lower bound on the residue cardinality
proves `Q ≠ 0`. The proof forms the finite polynomial

`P(X) = Σ_{i=0}^n (c_i / Q^(i*(n-i))) * (-1)^i * X^i`.

Its coefficient at index `i` is precisely the displayed coefficient. Thus
`P(0) = 1`. All coefficients above `n` vanish, and the coefficient at `n` is
`c_n * (-1)^n ≠ 0`, so `P.natDegree = n`.
The factorization helper constructs its spectrum, and this degree equality
changes only the cardinality proof attached to the same multiset of units.
For every index, substituting `eulerPolynomial s = P` into
`standardHeckeScalar F s i` cancels the nonzero power of `Q` and uses
`(-1)^i * (-1)^i = 1`. Its scalar is therefore exactly `c_i`, proving the
required action on every vector of `V`.

## Provenance and dependency boundary

This is a direct algebraic proof of the published statement. Its mathematical
normalization agrees with Gross, *On the Satake isomorphism* (1998), section 6,
retained PDF pages 11–12: equations (6.2)–(6.3) describe the character on the
fixed line, Proposition 6.4 provides the broader Satake parameterization, and
(6.5)–(6.7), especially (6.7), give the normalized signed coefficient formula.
The registered source is `gross-1998-satake-isomorphism`, retained
`Gross--On the Satake isomorphism--1998.pdf`, SHA-256
`9bd0077b2057edd32885e46fd38872f423a4d45fef6bec0aa181af32dee062b3`.

The implemented proof derives the needed existence directly from the published
fixed-line and double-coset theorems and Mathlib's complex polynomial splitting.
It does not invoke the Satake parameterization, spherical exhaustion, or a
converse principal-series/Hecke comparison. Its conclusion is the actual Hecke
spectral relation; principal-series realization and classification remain
separate results. No new axioms or proof holes are introduced.
