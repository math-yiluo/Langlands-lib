# Closed embedding of actual norm-one rational quotients

`Langlands.Global.AdelicGroupPoints.normOneRationalQuotientClosedImmersion`
proves `NormOneRationalQuotientClosedImmersionStatement` in arbitrary universe
`u`. For a closed immersion \(f:G\to H\) of affine group schemes locally of
finite type over a number field \(F\), it proves that the canonical map
\(G(F)\backslash G(\mathbb A_F)^1\to H(F)\backslash H(\mathbb A_F)^1\)
is a closed topological embedding. Here the superscript \(1\) uses the
normalized idele norms of all algebraic characters defined over \(F\).

## Rational points and injectivity

The closed immersion induces a closed embedding on adelic points. Restriction
to the closed source norm-one subgroup gives a closed embedding into the
ambient norm-one subgroup. For injectivity on the quotients, the Lean proof
first descends any rational point of \(H\) whose adelization lies in the source
image. The surjection of coordinate algebras induced by \(f\) has kernel
annihilated by the adelic evaluation at that point. Injectivity of the principal
diagonal \(F\to\mathbb A_F\) gives the same vanishing for rational evaluation,
which therefore factors through the coordinate algebra of \(G\). If two source
representatives become equal modulo a principal point in \(H\), this descent
supplies a principal point in \(G\) relating the original representatives.

## Finiteness of translates on a compact set

Chevalley's line-stabilizer theorem supplies an \(F\)-representation \(\rho\)
of \(H\) and a coordinate vector \(e\) whose line has stabilizer \(f(G)\) on all
test schemes. Restricting \(\rho\) to \(G\) gives its algebraic line character
\(\chi\), so \(\chi(p)\) has idele norm one for every \(p\in G(\mathbb A_F)^1\).
With the Library's left quotient convention, the continuous adelic vector map
sends \(y\) to \(\rho(y)e\). On \(qf(p)\) for \(q\in H(F)\), it takes the
value \(\chi(p)\) times the principal vector associated to \(\rho(q)e\).

Fix a compact set \(K\) in \(H(\mathbb A_F)^1\) and a compact set \(C\) of
representatives for norm-one ideles modulo principal scalars. If \(qf(p)\)
lies in \(K\), choose \(a\in F^\times\) with \(a\chi(p)^{-1}\in C\), viewing
\(a\) diagonally as an idele. The principal vector of \(a\rho(q)e\) belongs to
the compact image obtained by scaling the vector image of \(K\) by \(C\).
The Library's finiteness theorem for principal vectors in compact adelic
sets yields finitely many possible rational vectors \(a\rho(q)e\). If two
choices give the same vector, their rational group elements \(q,q'\) satisfy
\(q'^{-1}q\in f(G(F))\), by the line-stabilizer property on \(F\)-points.
Selecting one rational group element for each vector therefore supplies a
finite set of translates covering the intersections with \(K\).

## Closedness on the quotient

The inverse image of a closed subset of the source quotient is closed in
\(G(\mathbb A_F)^1\). The inverse image of its quotient image in
\(H(\mathbb A_F)^1\) is the union of the principal \(H(F)\)-translates of its
point image. Each translate is closed by the closed embedding on norm-one
points. On any compact neighborhood, the finite representatives above suffice
for this union because multiplication by each principal \(G(F)\)-point
preserves the lifted source subset. A closure point of the union is therefore
in the closure of a finite union of its closed translates on a compact
neighborhood, and belongs to the union. The quotient topology gives
closedness downstairs. The canonical map is already continuous, and closedness
and injectivity give the claimed embedding.

The adapted line and scalar compactness arguments come from T. A. Springer,
*Reduction theory over global fields* (1994), §§1.2–1.3, printed p. 208
(PDF p. 2). The registered source is `springer-1994-reduction-global-fields`,
SHA-256 `774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
Springer writes the rational cosets on the right. The proof above gives the
finite-translate and closed-map argument directly for left cosets.
