# Extending quotients to products with congruence groups

Let \(B\) and \(U\) be subgroups of a group \(G\), with \(B\) normalizing \(U\).
If \(q\colon B\to D\) is a group homomorphism trivial on \(B\cap U\),
`extendProductHom` extends it to \(B\vee U\) and sends \(U\) to the identity.
The construction uses the second isomorphism theorem
\(B/(B\cap U)\simeq (B\vee U)/U\). The extension restricts to \(q\) on \(B\)
and is surjective whenever \(q\) is. If \(\ker q=B\cap U\), then its kernel
is \(U\), viewed as a subgroup of \(B\vee U\).

For a simple stratum with \(r=0\) and a defining sequence, the module takes
\(B=U(\mathfrak B_\beta)\) inside \(\operatorname{Aut}_F(V)\). The
hereditary-order normalizer theorem shows that \(B\) normalizes every
ambient congruence subgroup. The simple-stratum product and normalizer
properties give \(J=B\vee J^1\) and show that \(B\) normalizes \(J^1\).
When \(\beta\) is scalar, the product equality follows from
\(J\subseteq U(\mathfrak A)=B\). The construction of the \(J\)-lattice
puts \(U^1(\mathfrak B_\beta)\) in \(J^1\), and
\(J^1\subseteq U^1(\mathfrak A)\) identifies both intersections with \(B\).

These identities allow any homomorphism on \(U(\mathfrak B_\beta)\) trivial
on \(U^1(\mathfrak B_\beta)\) to extend to \(J\) and to
\(U(\mathfrak B_\beta)U^1(\mathfrak A)\). A representation of the finite
relative quotient can then be pulled back along each extension.

The stratum identities use Bushnell and Kutzko, *The admissible dual of
GL(N) via compact open subgroups* (1993), §1.1, printed pp. 21–22
(PDF pp. 33–34), and (3.1.14)–(3.1.15), printed p. 95 (PDF p. 107).
The extension to \(U(\mathfrak B_\beta)U^1(\mathfrak A)\) is the group
homomorphism underlying the extension of the finite factor used in the
proof of (8.3.5), printed p. 296 (PDF p. 308).
The registered source is `bushnell-kutzko-1993-admissible-dual-gln`
with SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
