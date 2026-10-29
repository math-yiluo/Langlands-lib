# Proof of boundary cancellation and reflected defect rigidity

Worker 952 proves `Langlands.RankinSelberg.boundaryDefectRigidity` with exactly
the closed type `Langlands.RankinSelberg.BoundaryDefectRigidityStatement`,
defined in
[the statement module](BoundaryDefectRigidityStatement.md).

The proof introduces all variables and hypotheses of the statement.

1. **Factor the tails.** The divisibilities \(A\mid P\) and
   \(A^\vee\mid P^\vee\) are destructured as \(P=A\,S\) and
   \(P^\vee=A^\vee S^\vee\) (in Lean `S` and `Sd`).
2. **Cancel.** Since \(A(0)=1\), the polynomial \(A\) is nonzero, and likewise
   \(A^\vee\ne0\). Rewriting \(A\,C=D\,(A\,S)\) as \(A\,C=A\,(D\,S)\) and
   applying `mul_left_cancel₀` gives \(C=D\,S\). The same argument gives
   \(C^\vee=E\,S^\vee\).
3. **Normalize the defects.** Taking constant coefficients of \(P=A\,S\) with
   `mul_coeff_zero` and \(A(0)=1\) gives \(S(0)=1\). Taking constant
   coefficients of \(A\,C=D\,(A\,S)\) then gives \(D(0)=1\). Dually
   \(S^\vee(0)=1\) and \(E(0)=1\).
4. **Transfer root exclusions.** If \(|z|<a\) and \(D(z)=0\), then
   \(C(z)=D(z)S(z)=0\) by `eval_mul`, contradicting the hypothesis on \(C\).
   Hence \(D(z)\ne0\) for \(|z|<a\), and similarly \(E(z)\ne0\) for \(|z|<b\).
5. **Apply reflection rigidity.** The published theorem
   `Langlands.RankinSelberg.reflectionRigidity`, imported from
   `Langlands.Representation.RankinSelberg.ReflectionRigidityProof`, applies
   to \(D\) and \(E\) with the same \(a,b,\delta,c,m\), the positivity and gap
   hypotheses, the normalizations of step 3, the exclusions of step 4 and the
   unchanged rational reflection identity. It yields \(D=1\) and \(E=1\).
6. **Conclude.** Rewriting the original product identities with \(D=1\) and
   \(E=1\) gives \(P=A\,C\) and \(P^\vee=A^\vee C^\vee\).

No hypothesis is added to the target: the normalizations, root exclusions and
boundary factorizations of \(D\) and \(E\) are derived.

## Provenance

The argument in steps 1–4 and 6 is elementary internal cancellation. The only
substantive input is the published theorem
`Langlands.RankinSelberg.reflectionRigidity`
([its proof](ReflectionRigidityProof.md)), imported by Lean name; its
root-separation argument is not repeated here. The motivating source
(Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*, 1983,
section 9.4) and the obligations of any consumer are recorded in the statement
Markdown. This proof makes no further claim about that literature and supplies
no representation-theoretic or analytic input for applications.
