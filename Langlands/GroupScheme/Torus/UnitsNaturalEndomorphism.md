# Natural endomorphisms of families of units

Author: Worker 1122.

This module studies families of maps on unit families that are natural in the ring. It is
supporting algebra for `Langlands.GroupScheme.Rational.TorusNormalizerRigidity`, where the
family is conjugation by a torus-normalizing point written in the coordinates of a split
torus. Everything here is commutative algebra; no scheme appears.

## Objects

Fix `R : CommRingCat` and a type `I : Type u`.

- `laurentRing R I` is the Laurent polynomial ring `R[ℤ^I]`, that is
  `AddMonoidAlgebra R (I → ℤ)`. `laurentAlgebraMap R I : R ⟶ R[ℤ^I]` is its structure map.
- The existing `exponentUnit I m` from `Torus.UniversalPoint` is the invertible monomial `T^m = single m 1` with exponent vector
  `m : I → ℤ`. `UnitsNatEnd.universalUnits R I` is the family `j ↦ T_j` of the monomials
  `T^{e_j}`, where `e_j = Pi.single j 1`.
- For finite `I` and an exponent matrix `m : Matrix I I ℤ`, `powUnits m` is the monomial map
  on unit families of any commutative ring:
  `(powUnits m x) j = ∏ l, x l ^ m j l`.
  It is natural in ring maps (`powUnits_map`) and multiplicative (`powUnits_mul`). The
  identity matrix gives the identity (`powUnits_one`), and maps compose by matrix
  multiplication: `powUnits m' (powUnits m x) = powUnits (m' * m) x` (`powUnits_powUnits`).
  `powUnitsEquiv h₁ h₂` is the multiplicative equivalence given by an invertible matrix
  (`m' * m = 1`, `m * m' = 1`).
- `UnitsNatEnd R I` is a structure. Its field `app` gives, for every ring `A` under `R`
  (a morphism `α : R ⟶ A` of `CommRingCat`), a map `(I → Aˣ) → (I → Aˣ)`. The field
  `app_mul` says each map is multiplicative. The field `naturality` says the maps commute
  with every ring map `f : A ⟶ B` under `R`, acting on units by `Units.map f`.
  `naturality_of_eq` is the same statement with the structure map of `B` given by an
  equation.

## Coefficients of the universal family

For `φ : UnitsNatEnd R I`, `φ.coeffs j : R[ℤ^I]` is the `j`-th coordinate of
`φ.app (laurentAlgebraMap R I) (universalUnits R I)`. Its coefficients
`(φ.coeffs j).coeff m ∈ R` determine `φ`.

- `app_universalUnits`: over a ring `β : R ⟶ B`, the image of the universal family of
  `B[ℤ^I]` is the coefficient change of `φ.coeffs j` along `β`.
- `coeff_mul_coeff`: for fixed `j` the coefficients are orthogonal idempotents,
  `c m * c m' = if m = m' then c m else 0`. Consequently each coefficient is idempotent
  (`isIdempotentElem_coeff`).

Proof of `coeff_mul_coeff`. Work in `R[ℤ^I × ℤ^I]`. The families `x = ι₁(T)` and
`y = ι₂(T)` are the images of the universal family under the two inclusions
`m ↦ (m, 0)` and `m ↦ (0, m)`, and their product `xy` is the image under the diagonal
`m ↦ (m, m)`. Naturality computes `φ(x)`, `φ(y)` and `φ(xy)` as the images of `φ.coeffs j`
under these three ring maps, and multiplicativity gives `φ(xy) = φ(x) φ(y)`. Comparing
coefficients at `(m, m')`, with the helper lemmas `coeff_mapDomain_inl_mul_inr` and
`coeff_mapDomain_diag`, gives the identity.

## Comparison with monomial maps

`forall_app_eq_powUnits_iff β m` is the main theorem. For a ring `β : R ⟶ B` and an exponent
matrix `m`, the following are equivalent:

- for every ring map `f : B ⟶ A`, the map `φ.app (β ≫ f)` is `powUnits m`;
- for every `j`, `β ((φ.coeffs j).coeff (m j)) = 1`.

The forward direction evaluates at the universal family of `B[ℤ^I]` and uses
`powUnits_universalUnits`: the monomial map sends the universal family to the monomials
`T^{m j}`. For the converse, orthogonality forces all other coefficients to vanish in `B`,
so the coefficient change of `φ.coeffs j` is `T^{m j}`. A family `x` of units of `A` is the
image of the universal family under evaluation `B[ℤ^I] ⟶ A` at `x` (Library
`splitTorus.evaluateUnits`), and naturality transports the identity to `x`.

`exists_forall_coeff_eq_one`: over an integral domain `β : R ⟶ K` there is a matrix `m` with
`β ((φ.coeffs j).coeff (m j)) = 1` for all `j`. The coordinate `φ.coeffs j` maps to a unit of
`K[ℤ^I]`, so some coefficient is nonzero in `K`. That coefficient is an idempotent of a
domain, hence equal to `1`.

## Provenance

The module is internal infrastructure, proved directly from the definitions. It is the
algebraic core of a rigidity argument for split tori. Classically, Milne, *Algebraic Groups*
(2017), Theorem 12.36, printed p.243 (PDF p.259), states that a family of homomorphisms
between diagonalizable groups parametrized by a connected algebraic scheme is constant. Its
proof uses density of torsion subgroups. The argument here instead uses the idempotent
coefficients above and works over any base ring.
