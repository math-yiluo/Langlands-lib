# Complex conjugation commutes with unnormalized compact induction

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, IV.2.1, paragraph after Remark 2, printed p. 97 (PDF p. 103).
Registered source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`Langlands.Renard.CompactRepresentation.CompactInductionConjugateStatement`
formalizes the comparison in the modulus calculation before (IV.2.1.1).
For a smooth complex representation \(\rho\) of a closed subgroup \(H\) of a
t.d. group \(G\), with \(H\backslash G\) compact, there is a \(G\)-equivariant
complex-linear equivalence
\[
\overline{\operatorname{ind}_H^G(\rho)}
\ \simeq\ \operatorname{ind}_H^G(\overline{\rho}).
\]
On the conjugate of a function \(f\), its value at \(x\) is the conjugate of
\(f(x)\) in the conjugate coefficient space. The statement uses the original
unnormalized function induction `Induction.compactInduced` and the existing
`ConjSpace.rep`. The group and the coefficient carrier have independent
universes.
