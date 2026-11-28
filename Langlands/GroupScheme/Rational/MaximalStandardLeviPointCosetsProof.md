# Maximal standard Levi transporter cosets on rational points

`Langlands.GroupScheme.maximalStandardLeviPointCosets` proves
`Langlands.GroupScheme.MaximalStandardLeviPointCosetsStatement`.
The proof works over the nonarchimedean local fields of that statement and
uses the chosen maximal split torus and generic cocharacter.
[Statement](MaximalStandardLeviPointCosetsStatement.md)

## Proof

Apply `standardLeviTransporterCosets` to identify the Weyl transporter
cosets `StandardMaximalLeviWeyl.cosets I` (the image of \(W(L_I,*)\) in
\(W/W_I\)) with the rational-point transporter cosets for the given
standard Levi \(L_I\). An equivalence preserves `Nat.card`, so the
two-coset criterion of `standardMaximalLeviWeyl` (its clause
\(I\) maximal \(\iff \ell(I)=2\)) gives the required characterization of
maximal proper standard parabolics.

For a rational point \(g\) transporting \(L_I\) to \(L_J\), take the
inverse image of \(gL_I(k)\) under the equivalence. Its Weyl coset has a
representative \(n\) in the rational normalizer of the maximal split
torus. The representative rule of the equivalence gives
\(nL_I(k)=gL_I(k)\), so \(g=nh\) with \(h=n^{-1}g\in L_I(k)\).
Conjugation by \(h\) preserves \(L_I(k)\) and \(P_I(k)\supseteq L_I(k)\)
(`map_conj_mul`, `map_conj_eq_self_of_mem`, `levi_le_parabolic`), so
\(n\) transports \(L_I\) to the same \(L_J\) and conjugates \(P_I(k)\) to
the same subgroup as \(g\). If \(g\notin L_I(k)\), then
\(n\notin L_I(k)\), since otherwise \(g=nh\in L_I(k)\); by
`mk_mem_iff_mem_levi` the Weyl class of \(n\) lies outside \(W_I\).
The opposite-parabolic clause of `standardMaximalLeviWeyl` then applies
to \(n\) and any standard cocharacter \(\zeta\) of \(J\), giving
\(gP_I(k)g^{-1}=nP_I(k)n^{-1}=P(-\zeta)(k)\).
[Transporter comparison](StandardLeviTransporterCosetsProof.md) ·
[Maximal-Levi Weyl theorem](StandardMaximalLeviWeylProof.md)

## Correspondence with Renard

The opening of VII.1.3 considers a maximal standard Levi \(M\), recalls
from V.4.8 that maximality is equivalent to \(l(M)=2\), and states that
the set \(\mathcal W(M,*)\) of cosets \(gM\) with \(gMg^{-1}\) a standard
Levi has two elements \(\{1,w\}\), with
\(\mathcal W(M,*)\simeq W(M,*)/W_M\) in the notation of V.4.4. With
\(M'=w\cdot M\) and \(P'\) the standard parabolic with Levi factor \(M'\),
it states \(w\cdot P=\overline{P'}\), the parabolic opposite \(P'\).

In the Lean statement, \(M=L_I(k)\), \(\mathcal W(M,*)\) is the set
`pointCosets` of left cosets in the rational points, and \(\ell(I)=l(M)\)
is the cardinality of the Weyl-side set. The identification
\(\mathcal W(M,*)\simeq W(M,*)/W_M\) is `standardLeviTransporterCosets`;
the equivalence of maximality with \(l(M)=2\) and the opposite-parabolic
assertion on Weyl representatives are the V.4.8 results proved in
`standardMaximalLeviWeyl`. The proof above transports both to rational
points, which gives Renard's two-element count, together with its
converse, and the identity \(w\cdot P=\overline{P'}\) for every
representative \(w\) of the non-identity coset. Here \(M'=L_J\) for the
target index set \(J\). The opposite parabolic \(\overline{P'}\) is
written as the group of rational points of the dynamic parabolic
\(P(-\zeta)\), where \(\zeta\) is any standard cocharacter of \(J\):
mathematically \(P(\zeta)\) is the standard parabolic \(P'=P_J\), and
\(P(-\zeta)\) is its opposite with respect to the common Levi \(L_J\).
The proof uses this form of the conclusion as it is stated in
`standardMaximalLeviWeyl` and does not itself compare \(P(\zeta)\) with
\(P_J\).

## Source

David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026: VII.1.3 opening, printed p. 224
(PDF p. 230); V.4.8, printed p. 122 (PDF p. 128); V.4.3.3–V.4.4,
printed p. 119 (PDF p. 125).
Registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
