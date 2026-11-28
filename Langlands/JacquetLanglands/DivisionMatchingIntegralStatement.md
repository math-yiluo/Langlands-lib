# Haar integrals of matching regular-supported functions

`Langlands.JacquetLanglands.DivisionMatchingIntegralStatement` compares integrals on
`GL_n(F)` and `Dˣ`. The field `F` is nonarchimedean local of characteristic zero, and
`D` is a central division algebra of dimension `n²` over `F` with its `F`-module
topology. Both types range over the same arbitrary Lean universe `u`.

Give both groups their Borel σ-algebras and choose Haar measures `μ` on `GL_n(F)`
and `μ'` on `Dˣ`. Let `f` and `f'` be complex-valued and Bochner integrable for
their respective measures. `IsEllipticSupported f` requires `f` to vanish outside
the regular elliptic set, and `IsDivisionRegularSupported F D f'` requires `f'`
to vanish outside the regular set. If `AreMatching μ μ' f f'`, then

$$
\int_{\mathrm{GL}_n(F)} f(g)\,d\mu(g)
=
\int_{D^\times} f'(g')\,d\mu'(g').
$$

## Derivation

Apply the ordinary Weyl integration formula for integrable functions on each
group. Only elliptic maximal tori contribute on the split side by the support
condition, and every regular element of `Dˣ` is elliptic. Corresponding
elliptic tori are the unit groups of two copies of a degree-`n` extension `E/F`.
Their rational Weyl groups both identify with `Aut_F(E)`, as the normalizer
realizes every `F`-automorphism of `E` by conjugation. The Weyl discriminants at
corresponding regular elements agree because the eigenvalue ratios entering
the discriminant are determined by the common characteristic polynomial.

On a pair of corresponding tori, transport the Haar measure by the
isomorphism induced by the identification of the two copies of `E`.
The quotient measures in the Weyl formulas are compatible with `μ` and `μ'`
and those torus measures. `AreMatching` then identifies the inner orbital
integrals. Weyl integration applied to the norms of `f` and `f'` gives
integrability of those inner integrands for almost every torus element.
Thus the two Weyl sums agree with independently chosen ambient Haar measures.
This integral identity supplies the integration step in the matching trace
formula before character values are introduced.

## Sources

- Deligne–Kazhdan–Vignéras, *Représentations des algèbres centrales simples
  p-adiques* (1984), A.3, printed pp. 55–56, gives the ordinary Weyl formula for
  integrable functions and compatible quotient measures. B.2.a, printed p. 83,
  uses equality of matching orbital integrals to compare traces.
  Source `bdkv-1984-representations-local-field`, SHA-256
  `c1a4b4bd79575b5b41c15e1dacaf9a8094bd05c189efed06e27c62a64d22fcc3`.
- Badulescu, *Correspondance de Jacquet–Langlands pour les corps locaux de
  caractéristique non nulle* (2002), §5, printed p. 733, describes matching
  functions with compatible torus measures. Section 6, printed pp. 745–746,
  compares the elliptic torus terms and their measures in the scalar product
  of characters. The same comparison identifies the torus terms in the
  ordinary Weyl formula above. Source `badulescu-2002-jl-char-p`, folder
  SHA-256 `dc96cc7848166e83a1f23478a1e341928ea8565bc9b649ffe84e452f3a205028`.
  The cited file is
  `Badulescu--Correspondance de Jacquet-Langlands pour les corps locaux de caracteristique non nulle--2002.pdf`
  with SHA-256 `638e7134bb13c9c718ee7e5c2c9f06634637598c6ba8cd465345baf1234ed370`.
