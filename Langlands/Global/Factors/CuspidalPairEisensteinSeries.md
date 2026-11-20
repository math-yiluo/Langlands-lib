# Eisenstein series induced from a cuspidal pair

The namespace `Langlands.Global.CuspidalPairEisenstein` defines the normalized
sections, twisted Eisenstein sum, and generic coefficient at the identity for
the upper block parabolic \(P=MU_P\) of \(G=\mathrm{GL}_N\), with
\(n_1=r+1\), \(n_2=t+1\), and \(N=n_1+n_2\). The definitions specialize the
induced sections and Eisenstein series of Mœglin–Waldspurger, II.1.1–II.1.2
and II.1.5 (pp. 78–80, 85–86), to two actual cuspidal realizations and
the parameter in Shahidi, *On Certain L-Functions*, §2.3 and Theorem 5.1.
[Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*](https://doi.org/10.1017/CBO9780511470905.007)

## Normalized sections

`blockShape r t` orders the blocks as \((n_1,n_2)\). Its adelic Levi
embeds by \(m=(a,b)\mapsto\operatorname{diag}(a,b)\).
`dualRealization T'` chooses the actual full-operator contragredient supplied
by `Automorphic.cuspidalContragredientExistence` for \(T'\). The chosen
realization is cuspidal for every \(T'\), including when the central character
is nonunitary.

`IsSection T T' φ` requires a smooth archimedean slice of \(\phi\) at each
finite adelic point, invariance on the right by one open subgroup of the
finite adelic group, and finite-dimensional span of the right translates
by \(K=\texttt{standardCompact}\). These are the smooth and \(K\)-finite
conditions for the sections used in Shahidi §5 and in the compact picture
of Mœglin–Waldspurger II.1.1–II.1.2.

The remaining conditions are left \(U_P(\mathbb A_F)\)-invariance and the
requirement that for each \(k\in K\) the normalized Levi slice

\[
 (a,b) \longmapsto
 \delta_P(\operatorname{diag}(a,b))^{-1/2}
 \phi(\operatorname{diag}(a,b)k)
\]

belongs to the complex span of the products \(f(a)f^\vee(b)\) of cusp
forms from \(T\) and `dualRealization T'`. The Lean slice uses
`leviHalfCharacter` and evaluates the continuous rational-quotient functions
of the two realizations. Their carriers consist of archimedean compact-finite
forms. In the compact picture the algebraic tensor of those carriers gives
the slice at \(k\). For \(g=u m_0 k\), left unipotent invariance and the
character law identify the slice at \(g\) with
\(\delta_P(m_0)^{1/2}\) times the right translate by \(m_0\) of the slice
at \(k\). This gives the slice at every \(g\) in the smooth realization of
the inducing tensor. Right translation by a general archimedean Levi
element can lose compact finiteness. Evaluating the slice at the Levi
identity recovers \(\phi(g)\).

There are nonzero sections for every pair of realizations. Write
\(H=P(\mathbb A_F)\cap K\) and let \(V\) be the span of the cusp-form
products. The Levi projection gives \(H\) its action on \(V\).
Choose a nonzero vector given by a product of nonzero cusp forms. Its
archimedean \(H_\infty\)-translates span a finite-dimensional space, since
the forms are compact-finite and the Levi image of \(H_\infty\) is in the
product of the block compacts. Choose an irreducible \(H_\infty\)-type
in that space. Compact Frobenius reciprocity and Peter–Weyl give a
nonzero, smooth, right \(K_\infty\)-finite \(H_\infty\)-equivariant function
of \(k_\infty\) with values in this type. At the finite places choose a
compact open \(J_f\le K_f\) small enough that \(H_f\cap J_f\) fixes the
whole type. Extend the archimedean function to \(H_fJ_f\) by the
left \(H_f\)-action and right \(J_f\)-invariance and extend it by zero
on the other cosets. Archimedean and finite actions commute. The resulting
function on \(K\) is right \(K\)-finite because \(K_f/J_f\) is finite.

Iwasawa decomposition extends this function to \(G(\mathbb A_F)\) by
the block right-translation action and the factor \(\delta_P^{1/2}\),
using \(\delta_P|_H=1\). The extension is smooth in the archimedean
variables by the smooth local Iwasawa coordinates. Its evaluation
at the Levi identity gives a scalar section. Its normalized slice at each
\(k\) recovers the original value at \(k\) by right translation on the
realized functions. A nonzero value of the function on \(K\) is a nonzero
function of the Levi variable. Evaluating the scalar section at a
suitable \(m k\) therefore gives a nonzero value.

## Height and Eisenstein sum

The character `parabolicCharacter` is inflated from the Levi. Conjugation
on the upper rectangle of \(U_P\) sends \(X\) to \(aXb^{-1}\). The
absolute value of its determinant gives

\[
 \delta_P(\operatorname{diag}(a,b))
   =|\det a|_{\mathbb A_F}^{n_2}|\det b|_{\mathbb A_F}^{-n_1}.
\]

`heightPower F r t s g` uses a parabolic Iwasawa factorization
\(g=p k\), obtained from the published matrix Iwasawa theorem.
It is \(\exp((s/N)\log\delta_P(p))\) with the real logarithm of a
positive number. The Lean lemma `heightPower_eq` proves that every such
factorization gives the same value. The parabolic factors differ by an
element of \(P(\mathbb A_F)\cap K\), on which a continuous positive
character is trivial by compactness. In particular, for
\(g=u\operatorname{diag}(a,b)k\) this gives

\[
 H(g)^s
    =|\det a|_{\mathbb A_F}^{n_2s/N}|\det b|_{\mathbb A_F}^{-n_1s/N}.
\]

The weight \(2\rho_P\) is the sum of the roots across the two blocks,
with coefficients \(n_2\) in the first block and \(-n_1\) in the
second. Its pairing with the omitted simple coroot is \(N\).
Consequently \(\widetilde\alpha=2\rho_P/N\), and the twist is
\(\exp\langle s\widetilde\alpha,H_P(g)\rangle\) in the logarithmic Iwasawa
height convention. Shahidi (1981), §2.3, pp. 324–325, has \(a_1=N\),
so his variable \(z\) in the §5 expression \(L(1+a_1z,\cdots)\) is
\(s/N\) here.

`eisensteinSeries F φ s g` takes the unconditional sum of
\(\phi(\gamma g)H(\gamma g)^s\) over \(P(F)\backslash G(F)\), with
the zero value at a nonsummable family as in
`IsIwasawaCompact.eisensteinSeries`. For a section, the normalized
Levi slices are left rationally invariant, because each cusp form is.
The modulus is \(1\) on rational parabolic elements by the product
formula (`parabolicCharacter_rational`). The summand therefore descends
to the coset space. Right multiplication of the summation classes by a
rational element of \(G\) also shows that the sum is left \(G(F)\)-invariant.
This is the sum in Mœglin–Waldspurger II.1.5 with the above twist.

## Generic coefficient

`coeff ψ φ s` applies `generalLinearWhittakerFunction F (r+t+1) ψ (fun _ => 1)`
at the identity to the actual Eisenstein sum, using
`GeneralLinearGroupPoints.adelicEquiv`. It uses the entire upper
unitriangular group \(N_0\) of \(G\), with character
\(\psi_{N_0}(n)=\psi(\sum_{i=0}^{N-2}n_{i,i+1})\). The resulting integral is

\[
 \int_{N_0(F)\backslash N_0(\mathbb A_F)}
        E(\phi,s,n)\,\overline{\psi_{N_0}(n)}\,dn ,
\]

where \(dn\) is normalized quotient Haar measure.
`RankinSelbergGlobal.Unfolding.compactSpace_unipotentRationalQuotient`
gives compactness of this quotient. For a standard \(\psi\) the character
is trivial on \(N_0(F)\). Together with left rational invariance of the sum
for a section, this gives independence of the quotient representatives.
The coefficient specializes the Fourier-coefficient integral used in
Shahidi (1981), Theorem 5.1 proof, pp. 351–352.
