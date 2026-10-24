# Standard Hecke scalars determine spherical irreducible representations

This module shows that the standard spherical Hecke scalars determine an actual
irreducible admissible spherical representation up to equivalence, given the
generation statement `SphericalHeckeGenerationStatement`, so that the generation
statement implies `SphericalHeckeSpectrumDeterminationStatement`. It then derives
the spherical constituent uniqueness statement conditionally, from the constituent
Hecke-scalar statement and the determination statement. The local instances (field
topology, valuative relation, local field, group topology, topological group,
Hausdorff, Borel measurable structure) are the same as in `HeckeOperators`.

## Declarations

- `sphericalCornerAction F A` is the published `Hecke.cornerAction` of the whole
  spherical corner `SphericalHeckeAlgebra F r` on the actual fixed vectors
  `fixedVectors A.obj.representation (sphericalSubgroup F r)`, for the measure
  `sphericalHaar F r` and the open subgroup `sphericalOpenSubgroup F r`. It is the
  term of `standardHeckeOperator` without the element. So
  `sphericalCornerAction_standardHeckeElement` holds by `rfl`.
- `sphericalCornerAction_standardHeckeElement_of_hasSpectrum`: under
  `HasSphericalHeckeSpectrum F A s`, the element `standardHeckeElement F r i` acts
  as `algebraMap ℂ _ (standardHeckeScalar F s i)`.
- `standardHeckeScalar_last_ne_zero`: the scalar of `T_n`, `n = r + 1`, is nonzero.
  Its square-root power has exponent `n · (n - n) = 0`. Its elementary coefficient
  is `(-1)^n` times the coefficient of `X^n` of `eulerPolynomial s`. Since that
  polynomial is nonzero of natural degree `n` (`eulerPolynomial_ne_zero`,
  `eulerPolynomial_natDegree`), this coefficient is its leading coefficient.
- `eq_algebraMap_inv_mul_of_algebraMap_mul` cancels a nonzero scalar in a complex
  algebra.
- `exists_common_scalar_of_mem_adjoin`: if `A` and `B` both have spectrum `s`,
  every `f` in `Algebra.adjoin ℂ (Set.range (standardHeckeElement F r))` acts on
  both fixed spaces by one common scalar `c`. Proof: the product algebra
  homomorphism `P = (sphericalCornerAction F A).prod (sphericalCornerAction F B)`
  sends each generator into the bottom subalgebra `⊥`, the image of `algebraMap`
  (`Prod.algebraMap_apply`). By `Algebra.adjoin_le_iff` the adjoined subalgebra lies
  in `(⊥).comap P`, and `Algebra.mem_bot` gives `c`.
- `exists_common_scalar`: with the generation statement, the same holds for every
  `f` in the corner. Write `T_n^m f` in the adjoined subalgebra. Both actions of
  `T_n^m` are `algebraMap (t^m)` with `t ≠ 0`, so the common scalar is `(t^m)⁻¹ c`.
- `nonempty_equiv_of_hasSphericalHeckeSpectrum`: with the generation statement, two
  objects with the same spectrum `s` are equivalent. Choose nonzero fixed vectors
  `a` and `b` (`Submodule.exists_mem_ne_zero_of_ne_bot` applied to the first
  component of the spectral relation). Every corner element acts on `a` and `b` by
  one scalar `c`, so `e·a = 0 ↔ c = 0 ↔ e·b = 0`. The theorem
  `Hecke.nonempty_equiv_of_cornerAction_eq_zero_iff` (module
  `Langlands.Representation.Hecke.CornerDetermination`) applies, using smoothness
  `A.obj.isSmooth` and irreducibility `A.property.1`.
- `sphericalHeckeSpectrumDetermination_of`: the generation statement implies
  `SphericalHeckeSpectrumDeterminationStatement.{uF, uV, uW}` (module
  `Langlands.Representation.Unramified.SphericalHeckeSpectrumDeterminationStatement`),
  by the previous theorem.
- `sphericalConstituentUniqueness_of`: from
  `SphericalConstituentHeckeScalarStatement.{uF, uV}`, the same statement at
  `{uF, uW}`, and `SphericalHeckeSpectrumDeterminationStatement.{uF, uV, uW}`, derive
  `SphericalConstituentUniquenessStatement.{uF, uV, uW}`. A spherical constituent
  `A` of the principal series of `z` has spectrum `ofTuple z`, and `B` (for `w`) has
  spectrum `ofTuple w = ofTuple z`. The determination statement then gives the
  equivalence.

## Provenance

The argument is the standard one: spherical Hecke eigenvalues determine the
class-1 representation. See Borel, *Automorphic L-functions* (1979), 7.1–7.2,
printed pages 38–39 (source `borel-1979-automorphic-l-functions`). Gross, *On the
Satake isomorphism* (1998), section 6 (source `gross-1998-satake-isomorphism`),
states this through the Satake isomorphism. This implementation avoids the
Satake transform. It uses only the generation statement and the annihilator
form of Bernstein–Zelevinsky 2.10(b) proved in `CornerDetermination`.
