# Pullback of the dual extension for the second L-group twist

Let \(1\to B\xrightarrow{i} E\xrightarrow{p}D\to 1\) be a supplied abelian
group extension and let \(\kappa\colon A\to\operatorname{Hom}(B,\mathbf C^\times)\)
be a group homomorphism. `characterPullback i κ` is the subgroup of
\(A\times\operatorname{Hom}(E,\mathbf C^\times)\) given by
\[
  (a,\chi)\in\operatorname{characterPullback}(i,\kappa)
  \quad\Longleftrightarrow\quad \chi\circ i=\kappa(a).
\]
It is the equality locus of restriction on the second coordinate and \(\kappa\)
on the first. Its group law is the product group law, with pointwise
multiplication in the character coordinate. `pullbackFst` and `pullbackSnd`
are the two coordinate homomorphisms. `pullback_restriction` gives the
equality of their images in the character group of \(B\).

`secondTwist` constructs the short exact sequence with this middle group,
inclusion \(\psi\mapsto(1,\psi\circ p)\) and projection \((a,\chi)\mapsto a\).
The dual extension's injection proves injectivity on the character coordinate.
An element of the projection kernel has \(a=1\), so its character restricts
trivially to \(B\) and hence comes from \(D\) by the dual extension's middle
exactness. Surjectivity uses the dual extension's restriction map to lift
each \(\kappa(a)\) to a character of \(E\).

For a bimultiplicative pairing \(h\colon B\times A\to\mathbf C^\times\),
`pairingCharacter h` is the homomorphism \(\kappa(a)(b)=h(b,a)\), constructed
by flipping the curried homomorphism. `secondTwistOfPairing` uses this
\(\kappa\), and `mem_characterPullback_pairing` gives the restriction equation
\(\chi(i(b))=h(b,a)\) for every \(b\).

In Gan and Gao, *The Langlands–Weissman program for Brylinski–Deligne
extensions*, Astérisque 398 (2018), §5.2, (5.1)–(5.2), printed pp. 214–215
(PDF pp. 232–233), the local inputs are \(B=A=F^\times/(F^\times)^n\) and
\(h(b,a)=(b,a)_n\) with values viewed in \(\mathbf C^\times\). In §13.2,
printed p. 244 (PDF p. 262), the inputs are \(B=k^\times/(k^\times)^n\)
and \(A=\mathbb A^\times/(k^\times(\mathbb A^\times)^n)\), the quotient of
the idelic power classes by the image of \(k^\times\). The source supplies
the pullback map into the characters of \(B\). Both applications take the
arithmetic extension and character map as inputs to the algebraic construction.

The retained source has literature ID `gan-gao-2018-langlands-weissman-program`
and SHA-256 `fabbe056bdec2a5d57a22a0d3ad275640d0343c3f71092a7df427f7ebaebe892`.
