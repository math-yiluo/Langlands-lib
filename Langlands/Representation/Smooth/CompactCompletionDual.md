# The compact-open completion of the smooth contragredient

`Langlands.CompactCompletion.dualCompletionEquiv` identifies the algebraic
dual of a smooth complex representation with the compact-open completion
of its smooth contragredient. The group is a topological group in which
compact open subgroups are cofinal among open subgroups. The equivalence
intertwines the full dual action and translation of families and is natural
under pullback of functionals along smooth intertwiners.

This is the compact-open form of the dual completion in Renard,
*Représentations des groupes réductifs p-adiques*, French edition of 9 July
2026, I.4.3, printed p. 25 / PDF p. 31. VI.9.7, printed p. 206 / PDF p. 212,
applies that identification to a smooth group representation. The
registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The idempotents in the source are realized here by the normalized compact
averages of `CompactCompletion`.

The component at \(K\) of the family associated to a functional \(\ell\)
is \(\ell\circ e_K\). Right invariance of the average gives \(K\)-fixedness
under the dual action. Averaging a smooth functional transposes averaging
a vector, so these components satisfy the transition identities. The
inverse evaluates a family on a vector at any compact open index fixing
that vector. Passing to the intersection of two such indices proves
independence. Evaluation at an index fixing both vectors proves additivity,
and evaluation at an index fixing the vector proves scalar linearity.
Conjugation of averages gives equivariance. Commutation of an intertwiner
with averaging gives naturality.
