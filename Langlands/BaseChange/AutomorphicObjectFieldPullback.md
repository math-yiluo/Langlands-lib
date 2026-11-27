# Irreducible admissible representations along a field isomorphism

Let \(F\) and \(D\) be finite extensions of \(\mathbb Q_p\) and \(\mathbb Q_q\),
bundled as `PadicField p` and `PadicField q` with their canonical topologies, in
independent universes. Let \(a : F \to D\) be a ring isomorphism that is
continuous with continuous inverse. The primes are separate parameters. This covers the
completion of a number field, bundled over its residue characteristic, mapped
to a field bundled over a separately given prime. Write \(\kappa : GL_n(F) \to GL_n(D)\) for
the entrywise topological group isomorphism `generalLinearRingEquiv a`.

`fieldPullbackObject a ha ha' A` sends an irreducible admissible representation
\(A\) of \(GL_n(D)\) to the representation \(A \circ \kappa\) of \(GL_n(F)\) on
the same carrier. Smoothness, irreducibility and admissibility are preserved
by `isSmooth_comp`, `isIrreducible_comp_continuousMulEquiv_iff` and
`isAdmissible_comp_continuousMulEquiv`.

`AutomorphicObjectFieldPullbackStatement` records two properties.

1. If \(A\) is generic for a nontrivial unitary additive character \(\psi\) of
   \(D\), the pullback is generic for \(x \mapsto \psi(a(x))\), the character
   `FieldTransport.additiveCharacter a.symm ha ψ`. The map \(\kappa\) carries the
   upper unipotent group of \(F\) onto that of \(D\), since \(a\) preserves \(0\)
   and \(1\) and is injective. It carries the sum of the first superdiagonal to
   its image under \(a\). Thus the standard characters correspond, and
   `Whittaker.functionals_comp` identifies the two spaces of Whittaker
   functionals. A nonzero functional of \(A\) is therefore a nonzero functional
   of the pullback.
2. For a Haar measure \(\mu\) on \(GL_n(F)\), every endomorphism \(B\) of the
   carrier and every Schwartz–Bruhat function \(f\),
   \[
     \operatorname{tr}\bigl((A\circ\kappa)(f)\,B\bigr)_{\mu}
       = \operatorname{tr}\bigl(A(f\circ\kappa^{-1})\,B\bigr)_{\kappa_*\mu}.
   \]
   This is `twistedDistribution_comp_equiv` for \(\kappa\). The module also
   gives the ordinary case `fieldPullbackObject_distribution`.

`SigmaIntertwiner.ringPullback` treats twisted traces. Let
\(c : E_1 \to E_0\) be a ring isomorphism with \(c\circ\sigma_1 = \sigma_0\circ c\)
for algebra automorphisms \(\sigma_i\) of \(E_i\). Suppose that
\(\rho(g) = \tau(c(g))\) entrywise. Then a sigma-intertwiner of \(\tau\) for
\(\sigma_0\) is a sigma-intertwiner of \(\rho\) for \(\sigma_1\), with the same
linear map. The proof uses that the entrywise map of \(c\) intertwines the two
entrywise automorphisms.

These results transport local components of automorphic representations from
the completion of a number field to a given p-adic field. The local trace
comparison in Henniart–Lemaire, *Changement de base et induction automorphe
pour GLₙ en caractéristique non nulle* (2011), I.5.5 and I.6.9, printed
pp. 37–39 and 50–51, then applies to these local components. The construction
is an internal change of variables. It uses no additional source theorem.

Source ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
