# Scalar and determinant transport for the dominant reversed dual

This is internal support for the actual comparison in JPSS (1983),
Section 4.10(2)–(3), printed pp.419–420. The registered original is
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Those pages were visually reread for the section and determinant conventions.
The source registration and bounded registered-index/project-note checks found
no applicable correction. The lemmas here are derived compositions of existing
Library proofs, rather than a separately stated theorem from the source.

The source's induced and test ranks are `N=t+1` and `R=r+1` in Lean.
Write `c=j+k+1`, so `R=N+c`; `j,k` are arbitrary natural numbers,
including zero. The source illustrates the preceding integral derivation with
`k=0`, whereas the scalar and exponent algebra below permits every `j,k`.

For every field and real absolute value, the unsigned long Weyl matrix has
absolute determinant one by the existing `adjacentRank_abv_det_weylLong`.
`determinantWeight_longWeyl_inverseTranspose` combines this with the existing
multiplicative weight and inverse-transpose exponent laws. Thus, for
`Tg=w_N*inverseTranspose N K g`, its weight at an exponent `z` is the
original weight at `-z`. No branch identity for arbitrary complex bases is
assumed: the imported inverse-transpose law uses a nonnegative real absolute
value.

`dualDeterminantWeight` then proves, by cast normalization and ring algebra,

```text
weight(Tg, 1-s-(k+j+1)/2+k) = weight(g, s-(j+k+1)/2+j).
```

The equality holds for every complex `s`. `dualDeterminantWeight_zero`
compares both weights at parameter zero and obtains the extra factor
`|det g|`. Its proof specializes the preceding equality at original parameter
one and applies the existing exponent-addition law. For a canonical p-adic
field and a representative with determinant order `d`,
`dualDeterminantWeight_zero_onSlice` identifies this factor with `q^(-d)`,
where `q` is the canonical residue cardinality. These are weight identities;
no coefficient-integral reflection is inferred.

`reversedDualTest hr psi Wtest` defines the actual first dual function
right translated by `rightWeyl hr`, namely `diag(I_N,w_c)`.
`reversedDualTest_apply` exposes its value
`Wtest(w_R*inverseTranspose R K (P*rightWeyl hr))`.
`translatedDualTest_coefficient` realizes this test in the actual dual
coefficient model. For every representation `pi`, original positive
Whittaker functional `L` and vector `v`, it identifies the right-translated
first dual test with the coefficient of `inverseTransposePullback pi`,
functional `firstDualFunctional psi pi L`, and vector
`inverseTransposePullback pi (rightWeyl hr) v`. The proof rewrites by the
published dual coefficient identity, then uses representation
multiplicativity. Zero functionals and arbitrary representations are allowed.

`exists_reversedDualScalarRealization` uses the published
`twoBlockDualSectionJacquet` to choose one actual section equivalence `E`
before the character, inverse block functionals, test coefficient, section,
matrix and spectral parameter. The complete dependent family is reversed:
sizes, carriers, module instances and inverse-transpose block actions. Block
smoothness is its only representation hypothesis.

For `ellD i=secondDualFunctional psi (sigma i.rev) (ell i.rev)`, the first
clause states that

```text
rawScalarValue ellD (E f) (firstDualFunction psi r Wtest) (Tg) P
  = rawScalarValue ell f Wtest g (w_R*inverseTranspose R F P).
```

The proof applies the published scalar-section evaluation at the identity,
then proves `T(Tg)=g` by the group-map and unsigned Weyl involution laws.
The second clause includes the actual right translation on the dual test.
Its original test argument is
`w_R*inverseTranspose R F (P*rightWeyl hr)`. Multiplying by the
complementary dual weight at `1-s` gives the original scalar value times the
original weight at `s`, by `dualDeterminantWeight`.

The field, original test carrier and dependent block carriers have independent
universes wherever they occur. No irreducibility, nonzero functional,
Whittaker-type or quotient-measure assumption is added. The theorem is on
actual group representatives and makes no large-matrix comparison:
identifying its displayed argument at the reversed five-block matrix remains
a separate algebraic obligation. It supplies no rectangle or quotient
integration, convergence, determinant-coefficient reflection, Laurent
functional equation, gamma product or L-polynomial divisibility. Both final
dominant-rank propositions remain open.

The canonical local instances have module-specific names so that this module
can be imported together with the other dominant scalar, rectangle and slice
helpers. This naming correction changes no instance value or mathematical
definition, statement or proof.
