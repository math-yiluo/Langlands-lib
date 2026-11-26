# The relative Weyl group as a quotient of a subgroup of the extended Weyl group

`Langlands.GroupScheme.RelativeWeylQuotientStatement` concerns a
connected reductive group scheme \(G\) over any field \(k\), a maximal
\(k\)-split torus \(S\) of \(G\), and any extension \(K/k\). It takes a
maximal \(K\)-split torus \(T\) in \(G_K\) and a homomorphism
\(S_K\to T\) through which the base-changed inclusion factors.
When \(T\) is a split maximal torus, its Weyl group is the absolute
Weyl group.

Let \(D=N_{G_K}(S_K)(K)\cap N_{G_K}(T)(K)\). Its image in
\(W_T=N_{G_K}(T)(K)/Z_{G_K}(T)(K)\) is `toT.range`. The subgroup is
the image of actual normalizer points, whose conjugations restrict
as torus morphisms. The homomorphism `toS` sends a point of \(D\) to
its class in the Weyl quotient of \(S_K\). The conclusion gives a
surjective group homomorphism from `toT.range` to the relative Weyl
group \(N_G(S)(k)/Z_G(S)(k)\). For each point of \(D\), the image of
its class restricts on the test scheme \(\operatorname{Spec}K\) to the
class given by `toS`, transported by `fibreRelativeWeylGroupEquiv`.
Lean expresses this compatibility as equality of two group homomorphisms
from \(D\). The monomorphism used for the fibre comparison comes from
the closed immersion \(S\hookrightarrow G\) by base change.

## Source and derivation

Armand Borel and Jacques Tits, *Groupes réductifs* (1965), registered
source `borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
Corollary 5.5, printed p.97 (PDF p.44), obtains the relative Weyl group
by restricting \(N(S,T)/Z(T)\) to \(S\). Sections 5.1 and 5.3,
printed pp.95–97 (PDF pp.42–44), identify the Weyl groups and give
rational normalizer representatives. Over \(K\), the centralizer of
\(T\) centralizes \(S_K\), so the image in \(W_T\) realizes the
simultaneous normalizer quotient on rational points. The factorization
of the normalizer of \(S_K\) in Corollary 5.5 gives surjectivity, and
connected-test base change for \(S\) identifies the restriction with
the ground-field relative Weyl group.
