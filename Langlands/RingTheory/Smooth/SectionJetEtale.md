# Étaleness from isomorphisms on section jets

Let \(A\) be a finitely presented algebra over a noetherian ring \(P\).
Suppose both are algebras over \(R\) in a compatible tower and \(A\) has
an \(R\)-algebra augmentation \(\varepsilon\). Give \(P\) the composite
augmentation. If the maps on the quotients by all positive powers of the
augmentation ideals are isomorphisms, then \(P \to A\) is étale at every
prime of \(A\) obtained by pulling back a prime of \(R\) along \(\varepsilon\).

The compatible jet isomorphisms induce a \(P\)-algebra isomorphism of the
adic completions along the augmentations. The completion of \(P\) is flat
over \(P\). For each section prime \(q\) of \(A\), the augmentation on the
completion of \(A\) gives a prime above \(q\). The resulting map from \(A_q\)
to the localized completion is faithfully flat, so \(A_q\) is flat over \(P\).

The surjection on first jets gives \(q \subseteq pA + q^2\) for the prime
\(p \subset P\) under \(q\). Localization and Nakayama's lemma give
\(p A_q = q A_q\). The two augmentation maps identify the residue fields
at \(p\) and \(q\) with the residue field at the chosen base prime.
The local unramifiedness criterion and the local flatness criterion for
étaleness apply to \(P_p \to A_q\), which is essentially of finite
presentation. Formal étaleness composes with that of \(P \to P_p\).

This is a derived ingredient for the smoothness criterion along a section
in Raynaud, SGA 3, Exposé XV, Lemma 5.4, Gille–Polo recomposition,
pp. 267–268. The Lean result applies when a map of augmented algebras
supplies the jet comparisons used in the smoothness argument.
