# Local polynomial presentation

`Langlands.Algebra.LocalPolynomialPresentationStatement` states an intermediate
presentation used in the proof of Stacks Lemma 10.128.9 (tag 05UV). It does not
prove the presentation or the flatness criterion.

For a local homomorphism of commutative local rings \(R\to S\), if \(S\) is
essentially of finite type over \(R\), there are a natural number \(n\), a prime
ideal \(\mathfrak q\subset R[X_1,\ldots,X_n]\), and a surjective \(R\)-algebra
homomorphism
\[
f:B=R[X_1,\ldots,X_n]_{\mathfrak q}\longrightarrow S
\]
such that both \(R\to B\) and \(f\) are local homomorphisms. Thus the ordinary
first isomorphism theorem identifies \(S\) with \(B/\ker(f)\). This last
identification explains the interface; it is not an additional Lean conclusion.

The Lean type uses `MvPolynomial (Fin n) R` and its canonical
`Localization.AtPrime q`, with the prime-ideal instance provided by the
existential witness `hq`. The algebra structure on \(B\) is the canonical one
through the polynomial ring. The map `f` is an actual `AlgHom`, so its scalar
compatibility and its kernel are available to subsequent proofs. Surjectivity
and both local-map properties are explicit conclusions.

The universe levels of \(R\) and \(S\) are independent. The polynomial ring and
its localization live in the universe of \(R\); the surjective homomorphism may
have target in a different universe. There is no Noetherian, flatness, finite
presentation, or injectivity hypothesis.

## Provenance

This is a derived, explicitly extracted intermediate statement from the opening
paragraph of the proof of Stacks Lemma 10.128.9 (tag 05UV). That paragraph first
writes \(S=C_{\overline{\mathfrak q}}\) for a finite type \(R\)-algebra \(C\),
then presents \(C\) as a polynomial quotient to obtain \(S=B/J\). The locality
of the two maps follows from this construction and the local map \(R\to S\).

The first sentence of the source proof says “essentially of finite
presentation”, although hypothesis (2) of the displayed lemma is only
“essentially of finite type”. This interface uses the finite-type hypothesis:
no finite generation of \(J\) is asserted. Establishing that later finiteness is
one of the substantive remaining steps in 05UV.

The registered original is `stacks-algebra-flatness-criteria-2026-10-22`,
content SHA256 `4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
file `05UV.html`, displayed hypothesis (2) and the opening proof paragraph.
