# Standard Levi transporter cosets (Renard VII.1.3)

`Langlands.GroupScheme.StandardLeviTransporterCosetsStatement` states the
identification in the opening of VII.1.3 at the level of rational points.
Let \(G\) be connected reductive over a nonarchimedean local field \(k\), with
a maximal split torus \(T\) and a generic cocharacter determining the
standard Levi subgroups \(L_I\). For each \(I\), the proposition compares
\[
  W(L_I,*)/W_I
  \quad\text{and}\quad
  \{gL_I(k)\mid g\in G(k),\ gL_I(k)g^{-1}=L_J(k)
        \text{ for some standard }J\}.
\]
The first set is `StandardMaximalLeviWeyl.cosets`, the image of `WLstar`
in the quotient by `standardRelativeWeylGroup`. The second is the image
of the indicated rational-point transporters in `G(k) ⧸ L_I(k)`.
For every normalizer point \(n\) representing a Weyl coset in the first set,
the equivalence sends that coset to \(nL_I(k)\).

Renard uses this comparison for a maximal standard Levi. The proposition
takes every standard \(I\), as for the definition of \(W(L_I,*)/W_I\)
in V.4.4. The fixed-target case \(J=I\) is the comparison of V.4.3.3.
V.4.8 computes the Weyl-side cardinality for maximal standard Levis and
describes conjugation of the parabolic by a representative of the second
coset. [V.4.3.3 proof](StandardLeviNormalizerQuotientProof.md) · [V.4.8 proof](StandardMaximalLeviWeylProof.md)

The source calls the point transporter quotient a group. The
proposition formalizes its underlying set of left cosets. For example,
in split \(\mathrm{GL}_3\) take \(L_I\) with a \(\mathrm{GL}_2\) block
on coordinates \(\{1,2\}\) for the upper triangular Borel. The permutation
matrix \(g\) sending \(e_1\) to \(e_2\), \(e_2\) to \(e_3\), and \(e_3\)
to \(e_1\) sends that block to \(\{2,3\}\). Its square sends it to
\(\{3,1\}\), a block outside the standard Levi list. Thus the numerator
can fail closure under multiplication even for maximal \(L_I\).

Source. David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026. VII.1.3, first paragraph, printed p. 224
(PDF p. 230), with V.4.3–4, printed p. 119 (PDF p. 125), and V.4.8,
printed p. 122 (PDF p. 128). Registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
