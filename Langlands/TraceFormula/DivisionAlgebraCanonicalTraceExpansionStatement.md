# The ordinary trace expansion for the units of a central division algebra (statement)

The module `Langlands.TraceFormula.DivisionAlgebraCanonicalTraceExpansionStatement` defines
one proposition and proves nothing:

- `Langlands.TraceFormula.DivisionAlgebraCanonicalTraceExpansionStatement`.

It states the trace formula for the compact automorphic quotient of the unit group
\(G=\mathrm{GL}_1(A)\) of a finite-dimensional central division algebra \(A\) over a number
field \(F\). For every smooth compactly supported test function \(f\) on \(G(\mathbb A_F)\),
the operator \(R(f)\) on \(L^2(A_G G(F)\backslash G(\mathbb A_F))\) is trace class, and its
trace is a finite sum over rational conjugacy classes of centralizer volumes times orbital
integrals of the norm-one average \(f^1\) of \(f\). The statement contains no compactness
hypothesis, no condition on the support of \(f\) or on the classes (such as separability of
characteristic polynomials), and no second group.

## Notation from the Library

The module adds only the proposition above. Everything else is in the Library.

- `F : Type` is a number field (`[Field F] [NumberField F]`), and `A : Type` carries
  `[DivisionRing A] [Algebra F A] [FiniteDimensional F A] [Algebra.IsCentral F A]`: a
  finite-dimensional central division algebra over `F`.
- `Gₐ` is a local notation for `FiniteAlgebraUnits.groupScheme (Module.finBasis F A)`, the
  affine group scheme over `F` whose points in a commutative `F`-algebra `B` are the units of
  `B ⊗[F] A`. It is the same group scheme as in
  `DivisionAlgebraSimpleTraceComparisonStatement`.
- `hD : IsConnectedReductive Gₐ` is a witness that `Gₐ` is connected reductive. The statement
  is quantified over every such witness, which the canonical constructions below take as an
  argument.
- `AdelicGroupPoints F G` is \(G(\mathbb A_F)\), `normOneSubgroup F G` is
  \(H = G(\mathbb A_F)^1\) (the common kernel of the adelic absolute values of the rational
  characters), and `rationalNormOneSubgroup F G` is the image \(\Gamma\) of \(G(F)\) in
  \(H\).
- `IsAdelicTestFunction F G f` is the Library's notion of a smooth compactly supported test
  function on \(G(\mathbb A_F)\) (Bernstein–Lapid, Example 3.1): `f` is continuous with
  compact support, its archimedean slices are plot-smooth, and it is invariant on the right and
  on the left under an open subgroup of \(G(\mathbb A_{F,f})\).
- `canonicalIntegratedAction F G hD f hf` (defined in
  `Langlands.TraceFormula.DivisionAlgebraSimpleTraceComparisonStatement`) is
  \(R(f)\varphi=\int f(g)R(g)\varphi\,dg\) on the canonical
  \(L^2([G])\), \([G]=A_G G(F)\backslash G(\mathbb A_F)\), for `Measure.haar` on
  \(G(\mathbb A_F)\); `hf` is the integrability of `f` for this measure.
- `canonicalNormOneAverage F G hD f` (same module) is
  \(f^1(x)=\int_{A_G} f(ax)\,da\) on \(H\), where \(da\) is the Haar measure on \(A_G\) whose
  product with `Measure.haar` on \(H\) is carried to `Measure.haar` on \(G(\mathbb A_F)\) by
  multiplication.
- `IsTwistedConjugate Γ (MonoidHom.id H) δ δ'` says that \(\delta'=h^{-1}\delta h\) for some
  \(h\in\Gamma\): ordinary \(\Gamma\)-conjugacy.
- `IsTraceClass` and `operatorTrace` are the Library's trace-class predicate and trace.
- `SimpleTraceGeometricExpansion Γ θ μH f t r`
  (`Langlands.TraceFormula.SingleOrbitSimpleTrace`) is the measure quantification of the
  geometric side of the simple trace formulas. For \(\theta\) the identity, with
  \(C_j\) the centralizer of \(r_j\) in \(H\) and \(D_j=\Gamma\cap C_j\), it says: for all
  right-invariant measures \(\mu_{C_j}\) on \(C_j\) that are finite on compact sets and
  positive on nonempty open sets, all measures \(\nu_{C_j}\) on \(C_j\backslash H\) compatible
  with \(\mu_H\) and \(\mu_{C_j}\) in the Weil integration formula (`IsCompatible`), and all
  measures \(\nu_{D_j}\) on \(D_j\backslash C_j\) compatible with \(\mu_{C_j}\) and the
  counting measure, each volume \(\nu_{D_j}(D_j\backslash C_j)\) is finite, each orbit
  function \(x\mapsto f(x^{-1}r_jx)\) is \(\nu_{C_j}\)-integrable on \(C_j\backslash H\), and
  \[
  t=\sum_j \nu_{D_j}(D_j\backslash C_j)\int_{C_j\backslash H} f(x^{-1}r_jx)\,d\nu_{C_j}(x).
  \]
  The right side does not depend on the choice of \(\mu_{C_j}\): rescaling it rescales the
  volume and the orbital measure inversely.

## Statement

For every `F`, `A` and `hD` as above, every `f : AdelicGroupPoints F Gₐ → ℂ` with
`IsAdelicTestFunction F Gₐ f`, and every witness `hf` that `f` is integrable for
`Measure.haar` on \(G(\mathbb A_F)\):

1. `canonicalIntegratedAction F Gₐ hD f hf` is trace class;
2. with \(H\), \(\Gamma\) and \(f^1\) as above, there are \(m\in\mathbb N\) and
   \(r:\{0,\dots,m-1\}\to\Gamma\) such that
   - the \(r_j\) are pairwise not \(\Gamma\)-conjugate;
   - for each \(j\) there is \(x\in H\) with \(f^1(x^{-1}r_jx)\neq 0\);
   - every \(q\in\Gamma\) such that \(f^1(x^{-1}qx)\neq0\) for some \(x\in H\) is
     \(\Gamma\)-conjugate to some \(r_j\);
   - `SimpleTraceGeometricExpansion` holds for \(\Gamma\), the identity twist
     `MonoidHom.id H`, the measure `Measure.haar` on \(H\), the function \(f^1\), the value
     `operatorTrace` of `canonicalIntegratedAction F Gₐ hD f hf`, and the family \(r\).

So \(r\) lists, once each, exactly the rational conjugacy classes on whose \(H\)-orbit \(f^1\)
is somewhere nonzero, and, for all compatible measures,
\[
\operatorname{tr} R(f)=\sum_j \operatorname{vol}\big((\Gamma\cap H_{r_j})\backslash H_{r_j}\big)
\int_{H_{r_j}\backslash H} f^1(x^{-1}r_jx)\,dx .
\]

## Mathematical source

This is the Selberg trace formula for compact quotient, J. Arthur, *An introduction to the
trace formula*, in *Harmonic Analysis, the Trace Formula, and Shimura Varieties*, Clay
Mathematics Proceedings 4 (2005), §1, (1.1)–(1.4), printed pp. 8–9 (PDF pp. 20–21 of the
registered volume `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`), applied to the
unimodular group \(H=G(\mathbb A_F)^1\) and its discrete subgroup \(\Gamma\). The ingredients
are as follows.

- **Compactness.** Since \(A\) is a division algebra, every \(F\)-split torus of \(G\) is
  central: such a torus acts on \(A\) by conjugation through algebra automorphisms, so a
  weight vector for a nonzero weight is nilpotent, hence zero, and the torus acts trivially.
  Hence the only parabolic \(F\)-subgroup of \(G\) is \(G\), that is, \(G\) is
  anisotropic in the sense of Springer,
  and \(\Gamma\backslash H=G(F)\backslash G(\mathbb A_F)^1\) is compact by the compactness
  theorem (C) of T. A. Springer, *Reduction theory over global fields*, Proc. Indian Acad.
  Sci. (Math. Sci.) 104 (1994), stated in §2.1 (printed p. 212, PDF p. 6), whose sufficiency
  half is proved in §3.5 (printed p. 215, PDF p. 9). The registered source is
  `springer-1994-reduction-global-fields`, SHA-256
  `774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`; the note
  `notes/errata/springer-1994-reduction-global-fields.md` records gaps in a literal
  transcription of §§2.3–2.6, which §3.5 uses, without disproving the theorem. Since
  \(G(\mathbb A_F)=A_G\times H\), the canonical quotient \([G]\) is identified with
  \(\Gamma\backslash H\).
- **Norm-one normalization.** Under this identification, integrating first over \(A_G\) shows
  that \(R(f)\) is the operator of \(f^1\) on \(L^2(\Gamma\backslash H)\) for `Measure.haar` on
  \(H\). This is why the expansion uses \(f^1\) and `Measure.haar` on \(H\).
- **Trace class.** On a compact quotient a compactly supported continuous test gives an
  operator with a bounded continuous kernel, hence a Hilbert–Schmidt operator. By the
  Dixmier–Malliavin theorem a smooth compactly supported test is a finite linear combination
  of convolutions of two such tests, so \(R(f)\) is a finite linear combination of products of
  two Hilbert–Schmidt operators and is trace class. This is the last step of the proof of
  J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024),
  Lemma 9.3.3 (printed pp. 247–248, PDF pp. 259–260).
- **Geometric expansion.** Arthur's computation on printed pp. 8–9 writes
  \(\operatorname{tr}R(f)=\int_{\Gamma\backslash H}\sum_{\gamma\in\Gamma}f^1(x^{-1}\gamma x)\,dx\)
  as \(\sum_{\{\gamma\}}\operatorname{vol}(\Gamma_\gamma\backslash H_\gamma)
  \int_{H_\gamma\backslash H}f^1(x^{-1}\gamma x)\,dx\). Only finitely many classes contribute:
  let \(K\) be a compact set with \(H=\Gamma K\) and \(S\) the compact support of \(f^1\);
  if \(\gamma\in\Gamma\) and \(f^1(x^{-1}\gamma x)\neq0\), write \(x=\delta k\) with
  \(\delta\in\Gamma\) and \(k\in K\); then \(\delta^{-1}\gamma\delta\) lies in the finite set
  \(\Gamma\cap KSK^{-1}\).
- **Measures.** The volumes and orbital integrals use compatible centralizer and quotient
  measures, as in Getz–Hahn, Corollary 18.4.1 and the measure normalization after it (printed
  p. 485, PDF p. 492). The registered source is
  `getz-hahn-2024-automorphic-representations`, SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

## Related statements in the Library

- `Langlands.TraceFormula.GroupSchemeCompactQuotientTraceFormulaStatement` states the trace
  formula on a compact positive rational quotient of a general affine group scheme, for a
  chosen central split torus. It assumes compactness of the quotient, takes for `f` a
  convolution \(f_1*f_2\) of two compactly supported continuous functions, and also asserts a
  spectral expansion. The present statement concerns the unit group of a division algebra,
  where no compactness hypothesis is needed, takes every smooth compactly supported test on
  the canonical quotient, and asserts only the trace-class property and the geometric
  expansion.
- `Langlands.TraceFormula.DivisionAlgebraSimpleTraceComparisonStatement` compares the trace of
  \(R(f')\) on \(L^2([\mathrm{GL}_1(A)])\) with that of \(R_{\mathrm{disc}}(f)\) for
  \(\mathrm{GL}_n\). The present statement expands the first of these traces geometrically,
  with the same `canonicalIntegratedAction` and `canonicalNormOneAverage`.
