# Regular elliptic elements of `GL_n(F)` correspond to units of `D`

The module
`Langlands.JacquetLanglands.CorrespondenceInputs.RegularEllipticCorrespondence`
states one proposition, `RegularEllipticCorrespondenceStatement`, and does not
prove it. Let `D` be a central division algebra of dimension `n²` over a
nonarchimedean local field `F`. Then every regular elliptic element of
`GL_n(F)` corresponds to a unit of `D`. This is the surjectivity of the
bijection between the regular elliptic conjugacy classes of `D^×` and of
`GL_n(F)`. Deligne–Kazhdan–Vignéras (DKV) recall this bijection at the start
of their paper, and Badulescu writes it out in the Annexe of his 2002 paper.

## Notation

- `F` is a nonarchimedean local field: `[Field F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F]` (the Mathlib class),
  of any characteristic.
- `D` is a finite-dimensional central division algebra over `F`:
  `[DivisionRing D] [Algebra F D] [FiniteDimensional F D]
  [Algebra.IsCentral F D]`. No topology on `D` is involved. `F` and `D` both
  live in `Type u`.
- `GeneralLinear n F` is `GL_n(F)`.
- The following are in `Langlands.JacquetLanglands.RegularElliptic`:
  - `IsRegularElliptic g`: the characteristic polynomial of the matrix `g` is
    separable and irreducible over `F`.
  - `IsRegular F D g'`: the reduced characteristic polynomial
    `reducedCharpoly F D (g' : D)` is separable.
  - `Corresponds F D g g'`: `g` is regular elliptic, `g'` is regular, and
    the characteristic polynomial of `g` equals the reduced characteristic
    polynomial of `g'`.
- The reduced characteristic polynomial is monic of degree
  `reducedDegree F D`, and `Module.finrank F D` is the square of this degree.

## The statement

`RegularEllipticCorrespondenceStatement` says the following. Let `F` be a
nonarchimedean local field, `D` a finite-dimensional central division algebra
over `F`, and `n` a natural number with `Module.finrank F D = n ^ 2`. Then
for every `g : GeneralLinear n F` with `IsRegularElliptic g` there is
`g' : Dˣ` with `Corresponds F D g g'`.

## Why the statement is true

Let `P` be the characteristic polynomial of `g`. It is monic, separable and
irreducible of degree `n`, so `L = F[X]/(P)` is a separable field extension
of `F` of degree `n`. Its constant term is `P(0) = (-1)^n det g`, which is
nonzero because `g` is invertible. Let `x ∈ L` be the image of `X`. Then
`P(x) = 0`, and `x ≠ 0` because `P(0) ≠ 0`. So `x` is a unit of the field
`L`. For `n ≥ 2` this already follows from the irreducibility of `P`. For
`n = 1` it is exactly the invertibility of `g`: then `P = X - a`, where
`a ≠ 0` is the entry of the `1 × 1` matrix `g`, and `x = a`.

By Serre, *Local Fields*, Chapter XIII, §3, Corollary 3 to Proposition 7
(printed p. 194), the class of `D` in the Brauer group of `F` has order `n`,
and every extension of `F` of degree `n` embeds in `D`. Serre's field is
complete for a discrete valuation with quasi-finite residue field, which
covers every nonarchimedean local field, of either characteristic. Serre
derives the embedding from Corollary 1 (printed p. 194): an extension of
degree `n` splits every class killed by `n`. A splitting field of degree `n`
is then isomorphic to a maximal subfield of `D`.

Let `ι : L → D` be an `F`-algebra embedding, and let `g' = ι(x)`. Since `x`
is nonzero and `ι` is injective, `g'` is a nonzero element of the division
ring `D`, hence a unit. Its minimal polynomial over `F` is `P`, the minimal
polynomial of `x`.
`g'` is a root of its reduced characteristic polynomial (Cayley–Hamilton for
the reduced characteristic polynomial, `Langlands.CentralDivision.aeval_reducedCharpoly`).
So `P` divides this polynomial.
Both are monic of degree `n`, hence equal. Therefore the reduced
characteristic polynomial of `g'` is separable and equals the characteristic
polynomial of `g`, which is `Corresponds F D g g'`.

The Library contains the Brauer-theoretic inputs of this argument:

- `Langlands.ClassFieldTheory.Local.addOrderOf_localDivisionClass`: the
  class of a local central division algebra of dimension `n * n` has
  additive order `n`.
- `Langlands.ClassFieldTheory.Local.scalarExtension_eq_zero_iff_degree_nsmul`:
  a finite extension `L` that is itself a nonarchimedean local field, with
  continuous structure map, kills exactly the classes `x` with
  `[L : F] • x = 0`. This is Serre's Corollary 1.
- `Langlands.CentralDivision.embeddingOfSplitOfReducedDegree`: a field
  extension of degree `reducedDegree F D` that splits `D` embeds in `D`.

## Derived content and differences from the sources

DKV, introduction §a (printed p. 33), state that there is a natural injection
`{G'} → {G}` of conjugacy classes of `G' = GL(m, D)` into those of
`G = GL(n, F)`. Restricted to the regular elliptic classes, it becomes a
bijection `{G'^ell} → {G^ell}`. DKV do not write out the map on that page.

Badulescu 2002, §6 (Annexe, printed p. 745), writes out this map for a
nonarchimedean local field `F` of any characteristic. Let `G` and `G'` be the
unit groups of two central simple algebras of the same dimension `n²` over
`F`, and call an element regular elliptic when its characteristic polynomial
over `F` is irreducible and separable. Badulescu states that sending an
element of `G` to its characteristic polynomial gives a bijection between the
regular elliptic conjugacy classes of `G` and the monic irreducible separable
polynomials of degree `n` over `F`, and that the same holds for `G'`.
Composing the two bijections matches the regular elliptic classes of `G`
with those of `G'`. Badulescu writes `g ↔ g'` when `g` and `g'` are regular
elliptic and have the same characteristic polynomial.

As written, the codomain is slightly too large. The characteristic
polynomial of a unit has nonzero constant term, so the correct common
codomain is the set of monic irreducible separable polynomials of degree `n`
over `F` with nonzero constant term. For `n ≥ 2` irreducibility already
forces the constant term to be nonzero, so the condition only matters for
`n = 1`. Then both algebras have dimension one, so they are `F`, and every
unit is a nonzero scalar `a`, with characteristic polynomial `X - a`. The
polynomial `X` is monic, irreducible and separable of degree one, but it is
the characteristic polynomial of no unit.
Badulescu leaves the condition implicit. With this codomain, the bijections
and the matching of classes hold as stated.

Take the two algebras to be `M_n(F)`, with unit group `GL_n(F)`, and `D`.
For `GL_n(F)`, the characteristic polynomial is the ordinary characteristic
polynomial of the matrix. For `D^×`, it is the reduced characteristic
polynomial. Let `g` be regular elliptic, with characteristic polynomial `P`.
Then `P` is monic, irreducible and separable of degree `n`, and its constant
term `(-1)^n det g` is nonzero. So `P` lies in the corrected codomain.
Badulescu's bijection for `D^×` then gives a regular elliptic conjugacy
class of `D^×` with reduced characteristic polynomial `P`. Any element `g'`
of that class has separable reduced characteristic polynomial equal to `P`,
which is `Corresponds F D g g'`. So the class form of the statement is in
Badulescu's text. The element `g'` that Lean quantifies is a representative
of the matching class.

This statement is the surjectivity of that bijection, phrased element by
element: no conjugacy classes appear, and the conclusion is the Library's
`Corresponds F D g g'`. For `D^×` the Library's `Corresponds` asks for a
regular `g'`, meaning one with separable reduced characteristic polynomial.
A unit with an irreducible separable reduced characteristic polynomial is
such an element. The argument above derives the statement from Serre's
Corollary 3. The statement holds for every nonarchimedean local field, not
only in characteristic zero, as in Badulescu's Annexe.

## Role

Mathematically, the statement serves the uniqueness of the
Jacquet–Langlands partner on the side of `GL_n(F)`. Suppose `A₁` and `A₂`
are both related to `B`. Then their characters agree at every regular
elliptic `g`, because each such `g` corresponds to some `g'`. A separation
theorem for characters of essentially square-integrable representations on
the regular elliptic set, such as the Library's
`Langlands.BaseChange.EllipticDiscreteTraceSeparationStatement`, then gives
`A₁ ≅ A₂`. This module does not carry out that argument.

## Sources

- Jean-Pierre Serre, *Local Fields*, GTM 67, Springer, 1979. Registered as
  `serre-1979-local-fields`, SHA-256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
  Chapter XIII, §3: Proposition 7 (printed p. 193, PDF page 198), and
  Corollaries 1 and 3 (printed p. 194, PDF page 199).
- P. Deligne, D. Kazhdan, M.-F. Vignéras, *Représentations des algèbres
  centrales simples p-adiques*, in J. N. Bernstein, P. Deligne, D. Kazhdan,
  M.-F. Vignéras, *Représentations des groupes réductifs sur un corps
  local*, Hermann, 1984, pp. 33–117. Registered as
  `bdkv-1984-representations-local-field`, SHA-256
  `c1a4b4bd79575b5b41c15e1dacaf9a8094bd05c189efed06e27c62a64d22fcc3`.
  Introduction §a, printed p. 33 (PDF page 37).
- A. I. Badulescu, *Correspondance de Jacquet–Langlands pour les corps
  locaux de caractéristique non nulle*, Ann. Sci. École Norm. Sup. (4) 35
  (2002), no. 5, 695–747. Registered as the publication folder
  `badulescu-2002-jl-char-p` (registered fingerprint
  `dc96cc7848166e83a1f23478a1e341928ea8565bc9b649ffe84e452f3a205028`).
  The file cited is the published PDF in that folder, SHA-256
  `638e7134bb13c9c718ee7e5c2c9f06634637598c6ba8cd465345baf1234ed370`
  (printed page = PDF page + 694). §6 (Annexe), printed p. 745 (PDF
  page 51): the matching of regular elliptic conjugacy classes of the unit
  groups of two central simple algebras of dimension `n²` by equality of
  characteristic polynomials.
