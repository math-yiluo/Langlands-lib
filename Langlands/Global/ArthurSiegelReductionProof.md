# Arthur's reduction lemma for compact Iwasawa subgroups

`Langlands.Global.ArthurTruncation.iwasawaSiegelReduction` proves
`IwasawaSiegelReductionStatement`. It uses the height of the given compact
Iwasawa subgroup $K$ and the given bijectivity of real character restriction
for $P_0$. For every choice of compact factors and chamber threshold $T_1$,
the conclusion concerns overlaps of the two points $x,\delta x$ in
$S^P(T_1,\omega)$, as in Arthur's application on p. 942.
[Statement and source conventions](ArthurSiegelSetsIwasawaStatement.md).

## Implemented proof

1. **Minimal-parabolic factors.** Write a Siegel point as $x=qak$ with
   $q\in P_0(\mathbb A_F)^1$, $a$ in the positive torus, and $k\in K$.
   The images of the unipotent and norm-one Levi factors have zero logarithm
   in $P_0$, so their product gives $q$. The Iwasawa height of $x$ is the
   height of $a$. The transpose of real character restriction identifies
   $\chi(H_0(x))$ with $\log|\chi(a)|$ for every torus character $\chi$,
   where $|\cdot|$ is the normalized idelic norm.
   [Iwasawa height](AdelicIwasawaHeight.md), [restriction and its transpose](ArthurParabolicSpaces.md).
2. **Height comparison in both directions.** The lift of the maximal split
   torus is central and maximal split in the minimal Levi. Springer's
   compactness theorem supplies a compact set of norm-one Levi representatives.
   The rational Levi decomposition and compactness of the unipotent rational
   quotient give compact representatives of $P_0(\mathbb A_F)^1$ modulo
   $P_0(F)$. Apply `exists_bruhat_height_bound_of_compactCover` to the
   inverses of $x$ and $y=\delta x$ for the two Bruhat decompositions of
   $\delta$ and $\delta^{-1}$. If $w$ is the relative Weyl class of $\delta$
   and $\psi$ is the torus character on the chosen line, the inequalities are

   $$
   |(w\psi)(a_y^{-1})|\le B|\psi(a_x^{-1})|,\qquad
   |(w^{-1}\psi)(a_x^{-1})|\le B|\psi(a_y^{-1})|.
   $$

   The inverses put the $K$ factors on the left. The constant $B>0$ comes
   from height distortion on compact sets and a positive lower bound on the
   adelic height of a nonzero rational vector.
   [Bruhat height comparison](AdelicSplitOverlapHeight.md), [minimal Levi compactness](AdelicSpringerCentralCompactnessProof.md).
3. **Support of the displacements.** Fix $\alpha\in S=\Delta_0^P$. Choose
   $\psi$ from the dominant line for $P_{\Delta_0\setminus\{\alpha\}}$.
   The simple reflections other than $s_\alpha$ fix $\psi$, and
   $\psi-s_\alpha\psi$ is a positive integral multiple of $\alpha$.
   The combinatorial displacement theorem gives $D(w)=\psi-w\psi$ as a
   nonnegative integral sum of simple roots. If $\delta$ lies outside
   $P_{\Delta_0\setminus\{\alpha\}}(F)$, the same theorem gives
   $D(w^{-1})-\alpha$ as such a sum. The Bruhat class of $\delta$ belongs
   to the Levi Weyl subgroup for $S$ because $\delta\in P(F)$. Both sums
   pair to zero with a standard cocharacter for $S$, which vanishes on $S$
   and is positive on every simple root outside $S$. Thus both sums use
   only roots in $S$.
   [Dominant line](../GroupScheme/Rational/MaximalParabolicLineDominance.md), [Weyl displacements](../GroupScheme/Rational/DominantWeylDisplacementRoots.md), [normalizer points in a parabolic](../GroupScheme/Rational/NormalizerParabolicPoints.md).
4. **A uniform threshold.** Add the logarithms of the two height inequalities
   and use the chamber lower bounds for the displacements supported on $S$.
   This gives

   $$
   \alpha(H_0(x))\le 2\log B-D(w)(T_1)-(D(w^{-1})-\alpha)(T_1).
   $$

   Take an upper bound over the finite relative Weyl group and then over
   the finite simple-root set. If $\alpha\in S\setminus S_1$, regularity and
   $\alpha(H_0(x)-T)>0$ put $\alpha(H_0(x))$ above this bound. Therefore
   $\delta\in P_{\Delta_0\setminus\{\alpha\}}(F)$ for every such $\alpha$.
   Intersect these standard parabolics with $P(F)$ to obtain $P_1(F)$.
   The intersection proof deletes one root at a time and uses the canonical
   closed representatives to identify the resulting rational image.
   [Intersections of standard parabolics](../GroupScheme/Rational/StandardParabolicIntersections.md).

## Sources

- J. Arthur, *A trace formula for reductive groups I* (1978), §6, printed
  pp. 941–942. Registered source `arthur-1978-trace-formula-reductive-groups-I`,
  SHA-256 `80ec482ea894e3af960e79cc1316ac2c2e806ad466f92c106650a59a0b2f17cc`.
  [Arthur, §6](https://www.claymath.org/library/cw/arthur/pdf/7.pdf#page=31).
- R. P. Langlands, *On the Functional Equations Satisfied by Eisenstein Series*
  (1976), Lemma 2.12 and its proof, pp. 23–24 of the retained copy. Registered
  source `langlands-1976-functional-equations-eisenstein-series`, SHA-256
  `0ea4f3186926ff92c590ce08cf7fc360297fea83e7d9231db614e3616619e0c9`.
  [Langlands, IAS publication page](https://publications.ias.edu/book/export/html/39).
- T. A. Springer, *Reduction theory over global fields* (1994), Proposition 2.6
  on p. 213 for the height comparison and §3.5 on p. 215 for the compactness
  argument. Registered source `springer-1994-reduction-global-fields`, SHA-256
  `774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
  [Springer, Proposition 2.6](https://math.stanford.edu/~conrad/conversesem/refs/springer.pdf#page=7).
