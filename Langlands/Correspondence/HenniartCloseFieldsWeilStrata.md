# Refined Weil orbit strata of close fields

Let \(F\) be a p-adic field of absolute ramification index \(e\), and
let \(X\) be the Laurent-series field over its residue field. For rank
\(n=k+1\), natural Swan exponent \(s<ne\), and torsion number \(f\),
`Langlands.Henniart.closeFieldsWeilRefinedStratumEquiv` identifies
the corresponding refined Weil strata of \(F\) and \(X\). The stratum
elements are unramified-twist orbits of continuous irreducible complex
classes. The field and representation-carrier universes are independent.

The proof chooses the filtered isomorphism of the two Weil quotients
at upper index \(e\) from `Ramification.Local.closeFieldsWeilQuotient`.
It uses the actual Laurent-series field and its separable closure. The
Swan cutoff criterion puts every class counted by either stratum among
the classes trivial on its upper group of index \(e\), including when
\(s=0\).

Transport through the quotient isomorphism preserves rank and preserves
the triviality test at each upper index \(r\in[0,e]\). At \(r>e\) both
classes are trivial on the upper group by monotonicity of the filtration.
Consequently the sets of nonnegative indices where the upper groups
act trivially agree, and their infima give the same last break. The Swan
comparison theorems identify the natural Swan witness on each side with
the rank times this break.

The geometric degree on the Laurent-series Weil group descends to its
quotient. Pulling it back through the isomorphism recovers the p-adic
degree, so transport intertwines the same complex-unit parameter of
each unramified twist. Invertibility identifies the sets of parameters
fixing the two classes and hence their torsion numbers.

The proof maps the bounded classes of the prescribed rank, exponent,
and torsion number onto each orbit stratum. Both maps are surjective
by the cutoff criterion and the class equivalence. Twist equivariance
and injectivity show that the maps have the same fibers. They induce the
stratum equivalence and `closeFieldsWeilRefinedStratum_encard` gives
equality of extended cardinalities. Its specialization
`closeFieldsWeilTwistIrreducibleCount` takes \(f=1\).

The proof follows the representation comparison in Henniart,
`henniart-1988-numerical`, SHA-256
`3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`,
§5.1, p. 512. The refined count at arbitrary \(f\) is the final
display of Theorem `thm:Deligne` in
`operator-numerical-llc-route-2026-11-16`, directory SHA-256
`faece16e4d4722c37c1ba0e7ebba30a11d94b64639f20f19a6aa7ccff3faba3f`,
`numerical-LLC-route.tex`, lines 861–872, using the strata at lines
182–201.

[Close-fields Weil quotients](../LocalFactor/Ramification/CloseFieldsWeilQuotientProof.md) ·
[Transport through quotients](../Weil/Representation/FilteredQuotientClassTransport.md) ·
[Swan cutoff](HenniartLocalWeilSwanBreak.md)
