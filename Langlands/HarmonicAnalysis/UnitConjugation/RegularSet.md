# The regular set of the Lie algebra of `Aˣ`

The module `Langlands.HarmonicAnalysis.UnitConjugation.RegularSet` defines Harish-Chandra's
regular set `g'` for the Lie algebra `A` of the unit group `Aˣ` of a finite-dimensional
associative algebra `A` over a field `F`, the Lie bracket being the commutator
`[X, Y] = X Y - Y X`. In the Library's harmonic analysis on `A` (the modules under
`Langlands/HarmonicAnalysis/UnitConjugation`) the adjoint action of `Aˣ` on `A` is conjugation
`X ↦ u X u⁻¹`, and `g'` is the set of regular points used by Harish-Chandra's results on regular
orbits.

## Definitions

All definitions are in the namespace `Langlands.HarmonicAnalysis.UnitConjugation`; `F` is a
field and `A` an `F`-algebra (`[Ring A] [Algebra F A]`), finite-dimensional for the last three.

- `adjointEndomorphism F X : A →ₗ[F] A`: the adjoint endomorphism
  `ad X = LinearMap.mulLeft F X - LinearMap.mulRight F X`, that is `Y ↦ X Y - Y X`
  (`adjointEndomorphism_apply`).
- `lieAlgebraRank F A : ℕ`: the rank `ℓ` of `A` as a Lie algebra. It is Mathlib's
  `LieAlgebra.rank F A` for the Lie ring structure `LieRing.ofAssociativeRing` (the commutator
  bracket) and Mathlib's Lie algebra structure `LieAlgebra.ofAssociativeAlgebra`. Mathlib
  defines it from the characteristic polynomial of `ad` of the generic element, whose
  coefficients are polynomial functions on `A`: `ℓ` is the least `n` such that the coefficient
  of `t^n` is not the zero polynomial.
- `adjointEta F X : F`: Harish-Chandra's `η(X)`, the coefficient of `t^ℓ` in the characteristic
  polynomial `LinearMap.charpoly (adjointEndomorphism F X) = det(t - ad X)`.
- `regularSet F A : Set A`: `g' = {X | η(X) ≠ 0}`.

## Results

- `adjointEndomorphism_eq_ad`: `adjointEndomorphism F X` is Mathlib's `LieAlgebra.ad F A X` for
  the commutator Lie algebra (from `LieAlgebra.ad_eq_lmul_left_sub_lmul_right`).
- `mem_regularSet_iff_isRegular`: `X ∈ regularSet F A` if and only if `X` is regular in
  Mathlib's sense, `LieAlgebra.IsRegular F X` for the commutator Lie algebra.
- `lieAlgebraRank_le`: `ℓ` is at most the multiplicity of the root `0` of `det(t - ad X)`, for
  every `X`; `mem_regularSet_iff`: `X ∈ g'` if and only if this multiplicity equals `ℓ`.
- `regularSet_nonempty`: over an infinite field, `g'` is nonempty (Mathlib's
  `LieAlgebra.exists_isRegular`), so the multiplicity `ℓ` is attained. Over a finite field it
  need not be: for the algebra of upper triangular `3 × 3` matrices over `𝔽₂` the coefficient
  of `t^ℓ` is a nonzero polynomial, but it vanishes at every `𝔽₂`-point, so `g'` is empty.
- `adjointEndomorphism_conj`: `ad (w X w⁻¹)` is the conjugate of `ad X` by
  `conjugationLinearEquiv F w`, conjugation `X ↦ w X w⁻¹` by the unit `w` as an `F`-linear
  automorphism of `A` (declared in `Langlands.HarmonicAnalysis.UnitConjugation.PairingHaar`);
  `charpoly_adjointEndomorphism_conj` and `adjointEta_conj`: `det(t - ad X)` and `η` are
  invariant under conjugation by units, since similar endomorphisms have the same
  characteristic polynomial; `conj_mem_regularSet_iff`: `g'` is stable under conjugation by
  `Aˣ`.

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15),
Introduction, printed p. 2 (PDF p. 17): "Let `ℓ` denote the (absolute) rank of `g`. For
`X ∈ g`, let `η_g(X)` denote the coefficient of `t^ℓ` in the polynomial `det(t - ad X)` where `t`
is an indeterminate. Then `η = η_g` is a polynomial function on `g`, and `η ≠ 0`. Let `g'` be the
set of all points `X ∈ g` such that `η(X) ≠ 0`."

The correspondence with the source:

- Harish-Chandra works over a field `F` of characteristic zero. For a finite-dimensional
  semisimple algebra `A` over such a field, `GL₁(A)` is a connected reductive group (over an
  algebraic closure `A` becomes a product of full matrix algebras and `GL₁(A)` a product of
  general linear groups); its `F`-points are `Aˣ`, its Lie algebra is `A` with the commutator
  bracket, and its adjoint action is conjugation `X ↦ u X u⁻¹`. The definitions here are made
  for any field and any finite-dimensional algebra; outside characteristic zero `GL₁(A)` of a
  semisimple algebra need not be reductive.
- Harish-Chandra's absolute rank `ℓ` is the dimension of a Cartan subalgebra of `g ⊗ F̄`, the
  least dimension of the generalized `0`-eigenspace of `ad X` over `X ∈ g ⊗ F̄`, which is the least
  `n` such that the coefficient of `t^n` in `det(t - ad X)` is a nonzero polynomial function on
  `g ⊗ F̄`. These coefficients are polynomials with coefficients in `F` in the coordinates of `X`,
  and a polynomial is nonzero on `g ⊗ F̄` exactly when it is nonzero as a polynomial. So `ℓ` is
  Mathlib's `LieAlgebra.rank F A`, defined by the nonvanishing of the coefficient polynomial;
  no extension of scalars is needed.
- `η` and `g'` are then literally Harish-Chandra's `η_g` and `g'`.

In characteristic zero, for a reductive Lie algebra, `η(X) ≠ 0` holds exactly when `X` is
regular semisimple; Harish-Chandra calls an orbit regular when it lies in `g'` (§4, printed
p. 30). This characterization is not stated or proved in the module.
