# Compact rational representatives for bounded-root parabolic products

This internal prerequisite constructs compact principal rational representatives
for an ordered product consisting of a norm-one parabolic factor, a bounded
torus factor and a compact ambient factor. It uses the original adelic point
groups, rational principal maps and topologies over every number field in the
same arbitrary universe.

The general theorem
`exists_isCompact_rational_mul_mem_normOne_mul_set_mul` considers actual
group-scheme maps \(T\to H\to G\), with \(G\) affine. Its hypotheses are a compact
norm-one rational cover of \(H\), a compact set of principal rational
representatives for a specified subset \(S\subseteq T(\mathbb A_F)\), and a
compact subset \(C\subseteq G(\mathbb A_F)\). It produces a single compact
subset of \(G(\mathbb A_F)\) meeting every principal rational left coset
represented in \(H(\mathbb A_F)^1 S C\).

The proof chooses compact representative sets \(K_H\) and \(K_T\) from the
hypotheses. Given \(p s c\), choose a rational \(t\in T(F)\) with
\(t s\in K_T\), and let \(t_H\in H(F)\) be its image. Principal rational points
belong to the full norm-one subgroup, so
\(p'=p t_H^{-1}\) is still in \(H(\mathbb A_F)^1\). Choose \(r\in H(F)\)
with \(r p'\in K_H\). Functoriality of the principal maps and cancellation give
\[
 r(p s c)=(r p')(t s)c.
\]
The right side belongs to the compact product of the two mapped representative
sets with \(C\). The rational point used on the left is the actual image of
\(r\) in \(G(F)\).

The specialization
`exists_isCompact_rational_mul_mem_emptyParabolic_rootBox_mul_compact`
takes the canonical minimal standard parabolic of a connected reductive group.
The chosen maximal split torus is also required to be a maximal torus, and the
cocharacter is generic. For \(b\geq1\), the torus subset is
`ambientNormOneRootBox`: its image has ambient norm one and its normalized
simple-root norms lie between \(b^{-1}\) and \(b\). The published split
minimal-parabolic compact-cover theorem supplies \(K_H\); the root-box
compact-representative theorem supplies \(K_T\). The actual torus factorization
through the canonical parabolic identifies the resulting ordered product with
the one in the conclusion, defined as `boundedRootParabolicProduct`.

The elementary restriction lemma
`exists_isCompact_normOne_rational_mul_mem_of_ambient` intersects any compact
ambient representative set with the closed norm-one subgroup. Every principal
rational translate of a norm-one point stays in that subgroup. Applying it to
the bounded-root product gives
`exists_isCompact_normOne_rational_mul_mem_emptyParabolic_rootBox_mul_compact`:
one compact subset of the original norm-one group represents all its points
that belong to the specified product. No norm-one hypothesis on the whole
compact factor \(C\) is needed for this restricted conclusion.

This is a derived composition of the imported Library results. It neither
asserts that arbitrary norm-one points have bounded-root representatives nor
proves the full reductive compactness theorem. Uniform root bounds and
fundamental-set coverage remain separate obligations.
