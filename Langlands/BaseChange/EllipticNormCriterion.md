# The regular elliptic norm criterion

`ellipticNormCriterion` proves `EllipticNormCriterionStatement.{u,v}`. For a regular elliptic
matrix over a characteristic-zero nonarchimedean local field `F`, its determinant is a norm
of a unit in the cyclic `F`-algebra `E` exactly when the matrix is a cyclic norm in the sense of
`IsNorm`.

## Proof

Let `p` be the characteristic polynomial of `γ`, and write `P = AdjoinRoot p` and
`x = AdjoinRoot.root p`. Irreducibility makes `P` a field. The power-basis norm formula and the
matrix determinant formula both give the constant coefficient of `p` multiplied by
`(-1)^n`. Thus `N_{P/F}(x) = det γ`, and `x` defines a unit.

`isNorm_iff_charpolyTensor_product` identifies the matrix norm condition with the existence of
a unit of `P ⊗[F] E` whose product of cyclic conjugates is `x ⊗ 1`.
`IsCyclicAlgebra.scalarExtension` gives the cyclic action on that tensor algebra. The proof
identifies the cyclic product with the embedded determinant norm for any cyclic algebra. The
product is fixed by the generator, hence comes from the base field. In a residue-field
coordinate, the powers of the generator are indexed by a factor and a power of the
wraparound automorphism. Taking the product over the wraparound powers gives the field norm
of that coordinate. Taking the product over the coordinates gives the determinant norm of
the algebra by the product formula. Applying this identity to `P ⊗[F] E` shows that `IsNorm`
is equivalent to membership of `x` in the image of its determinant norm on units.

The cyclic coordinates identify `E` with a positive number of copies of one cyclic field
extension `K/F`. A nonempty product of copies of an algebra has the same norm image on units
as a single copy. The product formula sends a tuple of units to the norm of their product,
and placing a unit in one factor and `1` in all others realizes the converse. Tensor product
commutes with the finite product. The proof then uses the cyclic coordinates of `P ⊗[F] K`
to replace its norm image by that of a residue field `L/P`.

The quotient `P ⊗[F] K → L` shows that the images of `P` and `K` generate `L`, so restriction
from `Gal(L/P)` to `Gal(K/F)` is injective. The proof equips `P` with its spectral local-field
structure over `F` and applies `restrictNormalHom_arithmeticFiniteArtin_normUnits`. It sends
the symbol of `x` for `L/P` to the symbol of `N_{P/F}(x)` for `K/F`. Injectivity and the
Artin kernel formula identify the two norm conditions. The same quotient argument applies
when `P ⊗[F] K` has several field factors.

## Sources

- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
  (1989), Chapter 1, Lemmas 1.3(i) and 1.4, printed pp. 8–9 (PDF pp. 22–23). These give the
  centralizer norm condition and its comparison by local reciprocity. Source
  `arthur-clozel-1989-base-change`, SHA-256
  `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
- Henniart–Lemaire, *Changement de base et induction automorphe pour GL(n) en caractéristique
  non nulle* (2011), I.2.1, printed pp. 10–11 (PDF pp. 18–19), and I.6.12, printed p. 53
  (PDF p. 61). These give the cyclic product coordinates, the determinant on the
  characteristic field and the elliptic norm criterion. Source
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, SHA-256
  `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
