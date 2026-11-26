# The cocharacter lattice of the maximal split torus from the Tits index

`Langlands.GroupScheme.TitsIndexSplitCocharactersStatement` concerns a
semisimple group scheme over an arbitrary field \(k\), with affine and
locally finite type structure map. Its `TitsIndexData` give a maximal
split torus \(S\), a maximal \(k\)-torus \(T\) containing \(S\), and a
based root datum for \(T_{k_s}\) over the separable closure \(k_s\).
The absolute simple roots \(\Delta\) come from that base. A simple
root lies in \(\Delta_0\) when its restriction to \(S\) is zero.

An actual cocharacter \(\mu:\mathbf G_{m,k_s}\to T_{k_s}\) is the
base change of a unique composite \(\mathbf G_{m,k}\to S\to T\) if and
only if its root pairings satisfy
\[
  \langle \alpha,\mu\rangle=0\quad(\alpha\in\Delta_0),\qquad
  \langle \sigma*\beta,\mu\rangle=\langle\beta,\mu\rangle
  \quad(\sigma\in\operatorname{Gal}(k_s/k),\ \beta\in\Delta).
\]
Here `root'` evaluates the character of the absolute root on the
cocharacter using the datum's integral pairing, which agrees with the
actual torus pairing. The action on simple roots is `TitsIndexData.star`,
induced by the full star action on the actual based datum.

## Source and derivation

J. Tits, *Classification of algebraic semisimple groups* (1966),
registered source `tits-1966-classification-algebraic-semisimple`,
SHA-256 `962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.
Sections 2.1–2.3, printed pp.38–39 (PDF pp.43–44), fix the tori, the
compatible orders and the star action. The equations labelled (1) in
§2.5.1, printed p.40 (PDF p.45), describe the split torus via the
vanishing of the characters in \(\Delta_0\) and of the differences
\(\beta-\sigma*\beta\). Pulling these equations back along a
cocharacter gives the two displayed integral pairing conditions.
The source of a cocharacter is connected and reduced, so a cocharacter
into the common kernel factors through its reduced identity component. Every
cocharacter of the split torus over \(k_s\) descends to \(k\).
The closed inclusion of \(S\) and injectivity of cocharacter base change
give the uniqueness in the statement.
