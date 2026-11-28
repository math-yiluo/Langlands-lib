# Base change of the \(GL_n\) block subgroup schemes

Let \(b:\operatorname{Spec}R'\to\operatorname{Spec}R\) be a morphism between
spectra of commutative rings. Let \(n\) be a finite index type with decidable
equality and let \(e:n\to\mathbb Z\) give the weights of the diagonal
cocharacter. Write \(P_R,Z_R,U_R\) for its block parabolic, Levi and
unipotent group schemes. The three isomorphisms
`GeneralLinear.blockParabolicBaseChangeIso`,
`GeneralLinear.blockLeviBaseChangeIso` and
`GeneralLinear.blockUnipotentBaseChangeIso` compare
\[
b^*P_R \simeq P_{R'},\qquad b^*Z_R \simeq Z_{R'},\qquad b^*U_R \simeq U_{R'}
\]
in `Grp (Over (Spec R'))`. The isomorphisms are over \(GL_{n,R'}\), using
`GeneralLinear.baseChangeIso` for the ambient general linear group. The
three lemmas ending in `_hom_comp` record this compatibility with the
ambient inclusions.

The group scheme isomorphisms use the pointwise block subgroup equalities
of `GeneralLinearBaseChange`. Pullback carries each original subgroup
representative to a representative of its base-changed functor.
Transport along the ambient isomorphism gives a second representative
of the corresponding block functor over \(R'\). The isomorphism of
representatives follows from the monomorphism and range conditions on
all test schemes.

`GeneralLinear.blockLimitHom_baseChange` compares the block diagonal
limit homomorphisms along the parabolic and Levi isomorphisms.
Both composites can be tested after inclusion in \(GL_{n,R'}\).
For a test scheme \(T\) over \(R'\), the point corresponding to a given
point of the pulled-back parabolic has the same matrix when \(T\) is
viewed over \(R\) and when it is viewed over \(R'\) using the parabolic
isomorphism. The two applications of
`GeneralLinear.pointsEquiv_blockLimitHom` take the block diagonal part
of this matrix over \(\Gamma(T,\mathcal O_T)\).
`GeneralLinear.blockLeviToParabolic_baseChange` and
`GeneralLinear.blockUnipotentIsoKernel_inclusion_baseChange` give the
inclusion squares for \(Z\to P\) and \(U\to\ker(P\to Z)\to P\),
respectively. These squares follow from cancellation against the
parabolic inclusion into \(GL_{n,R'}\) and the compatibility of the
ambient inclusions.

`GeneralLinear.blockMultiplicationIso_hom_baseChange` compares the
underlying relative scheme maps \((u,z)\mapsto uz\). It uses the canonical
product comparison \(b^*U_R\times b^*Z_R\to b^*(U_R\times Z_R)\) and the
three group scheme isomorphisms. After composition with \(P_{R'}\to
GL_{n,R'}\), both paths are the product of the transported maps of
the two factors into \(GL_{n,R'}\). The proof uses the pullback and
composition laws for subgroup multiplication and cancels the
parabolic monomorphism. All comparisons allow arbitrary \(b\) and
include nonreduced test schemes.

The block groups and projection come from the weight decomposition and
limit calculation in Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
2nd ed. (2015), Example 2.1.1 and its continuation, printed pp. 45–47
(PDF pp. 71–73). Conrad, *Reductive group schemes* (2014), Theorem
4.1.7(3) and the paragraph after Example 4.1.9, printed and PDF
pp. 113–114, gives the dynamic multiplication and the base-change
property of the subgroup functors. The squares here follow from those
identities applied to the existing block representatives.
