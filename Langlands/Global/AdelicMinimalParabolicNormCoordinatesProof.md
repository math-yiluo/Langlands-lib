# The minimal-parabolic norm-one coordinate homeomorphism

`Langlands.Global.AdelicSiegelFactors.minimalParabolicNormCoordinates` proves
`MinimalParabolicNormCoordinatesStatement` at arbitrary universe. The
homeomorphism takes the actual \(N(\mathbb A_F)\), \(M(\mathbb A_F)^1\) and
intrinsic positive points \(A_{T_0}\) to the part of \(P(\mathbb A_F)\) in
the ambient \(G(\mathbb A_F)^1\). Its value in \(G(\mathbb A_F)\) is the
ordered product of the three specified images.

The published Levi projection \(f\) on the parabolic image sends the
unipotent image to the identity and fixes the Levi image. The continuous map
\(p \mapsto (p f(p)^{-1}, f(p))\) takes the ordered product of a unipotent
point and a Levi point to their two images. Both inclusions are closed
embeddings on adelic points. The composite with recovery is their product
embedding, so ordered unipotent–Levi multiplication is itself an embedding.

The setup identifies the minimal Levi with the centralizer of \(T\). The
lift of \(T\) to the Levi is maximal split and central, hence a split
component. The published split-component decomposition gives a homeomorphism
\(A_T \times M(\mathbb A_F)^1 \simeq M(\mathbb A_F)\). The composite
\(T_0 \to T \to G\) is a closed immersion by its factorization through the
represented derived subgroup. Thus \(T_0 \to T\) is a closed immersion, and
the induced map \(A_{T_0} \to A_T\) is an embedding for the intrinsic
subspace topologies. Restricting the Levi homeomorphism along this map
embeds \(M(\mathbb A_F)^1 \times A_{T_0}\) into \(M(\mathbb A_F)\).
Centrality gives the order \(m a\), and functoriality identifies the
ambient torus factor with `positiveMap`.

The composition of the two embeddings gives the forward map into the
ambient group. Each factor lies in the parabolic image and in the ambient
norm-one group. For the Levi factor this follows from restricting ambient
characters to the Levi, and for the other factors it follows from the
triviality of the character restrictions. The iterated subgroup topology
therefore gives an embedding into `standardParabolicNormOneImage`.
Surjectivity is the published `IsSiegelAlgebraicSetup.hasMinimalParabolicNormFactors`.
That proof lifts the positive \(T\)-coordinate through \(T_0 \times Z_0
\to T\) and uses the split-component decomposition of \(G\) to show that
the positive \(Z_0\)-factor is the identity when the ambient point is
norm one. The surjective embedding is a homeomorphism with the original
ordered product as its forward map.

The coordinate statement is a derived interface for the parabolic factors
in T. A. Springer's *Reduction theory over global fields* (1994), §2.1,
printed pp. 211–212. The source uses the rational Levi decomposition and
the parabolic character-norm kernel in forming its fundamental set.
The Lean proof uses the intrinsic positive torus and the ambient norm-one
restriction of the published statement. The source is registered as
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
