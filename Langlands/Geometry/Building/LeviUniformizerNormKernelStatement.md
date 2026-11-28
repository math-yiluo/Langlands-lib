# The Levi uniformizer quotient and the ambient norm kernel

`Langlands.GroupScheme.CocharacterUniformizer.LeviUniformizerNormKernelStatement`
expresses Renard V.3.25 for a connected reductive group \(G\) over a
nonarchimedean local field \(F\), in either characteristic. The inputs are a
proper rational parabolic map \(p:P\to G\), the inclusion \(l:M\to P\) of
a rational Levi, its split component \(a:A\to M\), and the ambient split
component \(b:B=A_G\to G\). Properness is expressed by the all-test range of
\(p\) being different from the full subgroup functor.

The proposition gives a factor \(f:B\to A\) whose composite
\(B\to A\to M\to P\to G\) equals \(b\). Its map on \(F\)-points is injective
with proper image.
In the actual group \(A(F)\), let \(C=C_A\) be the common-uniformizer
section, let \(D=f(C_B)\), and let \(N\) be the inverse image of \( {}^0G \)
under the point map \(m:A(F)\to G(F)\). The subgroup \( {}^0G \) is the
common kernel of the norms of the rational characters of \(G\).
Write \(H=b(B(F))\) and \(Q={}^0G\,H\) in \(G(F)\).

The proposition states that \(D\subseteq C\), \(D\cap N=\{1\}\), and
\(C\cap m^{-1}(Q)=D(C\cap N)\). With \(K=D(C\cap N)\) viewed as a subgroup
of \(C\), it gives an injective homomorphism \(C/K\to G(F)/Q\) sending
the class of \(x\) to the class of \(m(x)\), and states that \(C/K\) is
finite. The existence theorem `parabolicRootPresentationExistence` supplies
a compatible root presentation for these inputs. For every such presentation,
there is a point of the published strict uniformizer cone
`CocharacterUniformizer.CAstrict` in \(N\). The strict inequalities are
\(|\alpha(x)|_F<1\) for the characters in \(\Delta(P)\), realized as the
restrictions of the complementary simple roots in that presentation.
Equivalently, the image of \(x\) in \(G(F)\) belongs to \( {}^0G \).

The quotients are abstract quotients of point groups. The source uses the
inclusions of \(B(F)\) and \(A(F)\) into \(G(F)\), so the inverse images
above express the source intersections inside the supplied point groups.

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, V.3.25, printed p. 117 (PDF p. 123).
The common-uniformizer section and the ambient quotient refer back to
V.2.5–V.2.6, printed pp. 107–109 (PDF pp. 113–115), and the strict
cone to V.3.21 and V.3.23, printed pp. 116–117 (PDF pp. 122–123).
Registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
