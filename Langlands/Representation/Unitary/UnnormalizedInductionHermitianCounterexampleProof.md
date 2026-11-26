# Unnormalized induction of the trivial upper Borel representation

Module `Langlands.Representation.Unitary.UnnormalizedInductionHermitianCounterexampleProof`.
The theorem
`Langlands.Renard.CompactRepresentation.unnormalizedInductionHermitianCounterexample`
proves [`UnnormalizedInductionHermitianCounterexampleStatement`](UnnormalizedInductionHermitianCounterexampleStatement.md).
The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, IV.2.1, paragraph after Remark 2, printed p. 97
(PDF p. 103). Registered source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Renard's calculation there gives
\(\operatorname{ind}_H^G(\tau^h)=\operatorname{ind}_H^G(\tau\otimes\delta_{H\backslash G})^h\)
and does not exhibit a particular counterexample. The proof below gives one,
using the closed-subgroup duality of III.2.7, printed p. 78 (PDF p. 84),
in the form `Induction.closedInductionSmoothDuality`.

## The counterexample

Take \(G=\mathrm{GL}_2(\mathbb Q_2)\), with the topology of
`PadicField.canonicalTopologicalData`, and \(H\) its upper Borel subgroup,
the parabolic of `BlockShape.singletons 2`. `BlockShape.isClosed_parabolic`
and `Parabolic.parabolicQuotientCompact` give closedness of \(H\) and
compactness of \(H\backslash G\). The trivial representation of \(H\) on
\(\mathbb C\) is smooth, and the standard inner product `innerₛₗ ℂ` is a
nondegenerate invariant Hermitian form on it, so the trivial representation is
Hermitian in the sense of the statement.

Its compact induction contains the constant function \(1\). This function is
smooth with stabilizer all of \(G\), and its projected support is compact,
being a closed subset of the compact quotient (`isClosed_quotientSupport`).
Evaluation at the identity shows that it is nonzero, and right translation
fixes it.

## The relative modulus is nontrivial

The private lemma `borel_modulus_ne_one` finds \(a\in H\) with
\(\delta_{H\backslash G}(a)\neq1\), for \(\mathrm{GL}_2\) over any \(p\)-adic
field. Right invariance of the Haar measure `RankinSelberg.generalLinearHaar`
makes Mathlib's modular character of \(G\) trivial. Since
`HarmonicAnalysis.Distribution.renardModular` is the inverse of Mathlib's
modular character (`renardModular_eq_inv`), Renard's relative character
\(\delta_{H\backslash G}=\delta_G|_H/\delta_H\), the Library's
`relativeModular`, equals Mathlib's modular character of \(H\). Then
`BlockShape.modularCharacter_eq` with `glBlockModulusHaar` identifies that
character with the parabolic modulus, and `CartanQuotient.delta_eq_parabolicModulus`
evaluates it on the diagonal element with uniformizer exponents \((1,0)\)
(`CartanQuotient.representativeBorel`). Its degree is \(1\), so the value is
\(q^{-1}\), where \(q>1\) is the residue cardinality.

## No fixed vector in the smooth dual

The private lemma `compactInducedTrivial_fixedDual_eq_zero` holds for any
closed subgroup \(H\) of a Hausdorff locally compact totally disconnected
group \(G\) and any \(a\in H\) with \(\delta_{H\backslash G}(a)\neq1\): a
vector of the smooth dual of the compact induction of the trivial
representation that is fixed by all of \(G\) is zero.

Write \(\chi\) for the complex character of \(\delta_{H\backslash G}\)
(`HarmonicAnalysis.HomogeneousFunctions.Renard.relativeCharacter`) and take
the smooth coefficient \(\rho=\chi^{-1}\otimes\mathbf 1\). The invariant
functional \(\nu\) of II.3.9 (`HomogeneousFunctions.Renard.invariantFunctional`)
is nonzero: if it were zero, both \(0\) and \(1\) would be the unique scalar
expressing \(\nu\) as a multiple of itself. Applying
`closedInductionSmoothDuality` to \(\rho\) gives a \(G\)-equivariant linear
isomorphism from \(\operatorname{Ind}_H^G(\widetilde\rho)\) onto the smooth
dual of the compact induction of \(\chi\otimes\rho\), which is the trivial
representation by `twist_twist_inv`. A \(G\)-fixed vector \(\ell\) of that
dual thus comes from a \(G\)-fixed function \(f\in\operatorname{Ind}_H^G(\widetilde\rho)\).
Right translation makes \(f\) constant. Covariance at \(a\) gives
\(f(1)=\widetilde\rho(a)f(1)\); evaluating at \(x\in\mathbb C\) and using
\(\rho(a^{-1})x=\chi(a)x\) gives \(f(1)(x)=\chi(a)\,f(1)(x)\). Since
\(\chi(a)\neq1\), \(f(1)=0\), hence \(f=0\) and \(\ell=0\).

## Conclusion

Suppose the unnormalized induction of the trivial representation carried a
nondegenerate invariant Hermitian form. `HermitianProof.pairingToSmoothDual`
sends the fixed constant function \(1\) to a vector of the smooth dual, and
`HermitianProof.pairingToSmoothDual_action` shows that this vector is fixed by
\(G\). By the previous section it is zero. Nondegeneracy makes the map
injective (`HermitianProof.pairingToSmoothDual_injective`), so the constant
function would be zero, a contradiction.
