# The depth-zero consumer for valid KP building data

`Langlands.Geometry.Building.DepthZeroConsumerStatement` is a proposition
about every nonarchimedean local field \(F\) of either characteristic, every
connected reductive \(F\)-group \(G\), every `D : KPBuildingDatum G` satisfying
`D.SatisfiesGroupAxioms`, and every facet \(x\) of its reduced building.
The ambient group is the original \(G(F)\) with its canonical topology
`rationalPointTopology F G.X`. All objects come from the facet interface in
[`Definitions`](Definitions.md).

- **Parahoric.** \(P_x=G_x^0(\mathcal O_F)\) equals
  `BuildingModelFamily.zeroFixer` at the index of \(x\), the pointwise fixer
  inside \(G(F)^0\). It is compact and open in \(G(F)\). The setwise
  stabilizer in \(G(F)\) and the pointwise fixer in \(G(F)^1\) are distinct
  constructions.
- **Reduction.** \(P_{x,0+}\) is the preimage in \(P_x\) of the radical's
  residue-field points. It is normal, compact and open in \(P_x\) with its
  subspace topology. The reduction \(r_x:P_x\to\bar G_x(k_F)\) is surjective
  with this kernel. The neutral special fibre maps to the connected
  reductive quotient \(\bar G_x\), whose point group \(\bar G_x(k_F)\) is
  finite. The stated multiplicative equivalence
  \(P_x/P_{x,0+}\simeq\bar G_x(k_F)\) sends the class of \(p\) to \(r_x(p)\).
- **Representations.** For any complex representation \(\sigma\) of
  \(\bar G_x(k_F)\), the inflation is \(\sigma\circ r_x\) and
  \(P_{x,0+}\) acts trivially. The compact induction of the inflation is
  smooth, in the sense of open vector stabilizers for a discrete
  representation space.
- **Intertwining.** For finite-dimensional complex \(\sigma\) on \(V\) and
  \(\tau\) on \(W\), put \(A=\mathrm{c\text{-}Ind}_{P_x}^{G(F)}\operatorname{infl}\sigma\)
  and \(B=\mathrm{c\text{-}Ind}_{P_x}^{G(F)}\operatorname{infl}\tau\).
  The statement gives an injective complex-linear map from
  \(\operatorname{Hom}_{G(F)}(A,B)\) to the functions
  \(\Phi:G(F)\to\operatorname{Hom}_{\mathbb C}(V,W)\). Its range is exactly
  the functions satisfying
  \[
  \Phi(p g q)=\operatorname{infl}(\tau)(p)\circ\Phi(g)\circ
    \operatorname{infl}(\sigma)(q)
  \]
  for all \(p,q\in P_x\), \(g\in G(F)\), whose nonzero support meets
  finitely many double cosets \(P_x g P_x\). The map sends \(T\) to the
  kernel \(\Phi(g)(v)=T(i_v)(g)\), where \(i_v\) is the unit function
  supported on \(P_x\) with value \(v\) at the identity.

The proposition is conditional on validity of the supplied datum and
asserts these conclusions for each of its facets. Combined with
`GroupAxiomsExistenceStatement`, it gives the depth-zero conclusions for
data on every connected reductive group in the stated scope.

## Sources and specialization

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Axiom 4.1.20
  and Definition 4.1.21 (printed p. 163, PDF p. 194) identify the neutral
  model and the zero-fixer. Axiom 4.1.22(3), (7) (printed p. 164,
  PDF p. 195) gives the reductive quotient of its neutral special fibre
  and the radical preimage. Section 13.2.6 (printed p. 470, PDF p. 501)
  gives the quotient identification by reduction. Remark 2.10.3
  (printed p. 122, PDF p. 153) describes compactness and openness of
  integral points over a locally compact field.
  Literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`,
  SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024. PDF p. 27
  gives the corrected axiom list of Definition 4.1.26, from which
  `SatisfiesGroupAxioms` uses the one-group clauses. PDF p. 49 corrects
  the ambient group of the separate maximal pro-\(p\) result in
  Proposition 13.5.2(1) to \(G(F)^0\).
  Literature ID `kaletha-prasad-2024-corrections`,
  SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
- Vignéras, *Représentations ℓ-modulaires d'un groupe réductif p-adique avec
  ℓ ≠ p* (1996), I.5.1–5.2 (printed pp. 38–39, PDF pp. 56–57) for compact
  induction and the unit functions, and I.8.5 (printed pp. 67–68, PDF
  pp. 85–86) for the linear kernel correspondence. The statement uses
  \(K=H=P_x\) and takes the inducing representations to be inflations
  through the KP reduction. Finite dimension over \(\mathbb C\) gives
  finite generation over the group algebra. The Library's
  `depthZeroInductionKernelEquiv` uses evaluation on the same unit
  functions. Its finite-support criterion comes from
  `compactInductionFiniteTypeKernel`.
  Literature ID `provided-74667a7cddb3bdafff85f01c658605ce7d929f6da73950d79457c46bcd761dd4`,
  SHA-256 `4d2daeee16515f994dfb04157915179b55b30d5bf2f874a16f13e7cb6fa7d657`.
