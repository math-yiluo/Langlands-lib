# Cancellation of Arthur’s partial truncation operators

`Langlands.Global.ArthurTruncation.truncationCancellation` proves
`Langlands.Global.ArthurTruncation.TruncationCancellationStatement`. It gives finite support for
both rational coset sums, the two cancellation identities and integrability of the constant-term
integrand in the relative identity. The proof works for each truncation parameter in the real
cocharacter space and for every compact subgroup satisfying the minimal Iwasawa decomposition in
the statement. [Statement](ArthurTruncationStatement.md)

## Relative cancellation

Fix a standard parabolic `P` and a left `P(F)`-invariant function `φ`. For `Q ⊆ R ⊆ P`, the
summand from partial truncation along `R` contains the constant term `φ_Q` and the hatted cutoff
`τ̂_Q^R`. This product is left `Q(F)`-invariant. The outer cutoff `τ_R^P` is left `R(F)`-invariant.
The height invariance comes from the change of minimal height under a rational parabolic
translate, which lies in the coroot span of that parabolic. The constant-term invariance follows
from conjugation on the unipotent radical quotient. [Height and finiteness](ArthurTruncationRelativeFiniteness.md)
[Constant terms](ArthurTruncationConstantTerm.md)

The support of the outer cutoff on `R(F) \ P(F)` is finite. For each outer representative the
hatted cutoff on `Q(F) \ R(F)` also has finite support. The proof expands the partial truncation
and combines the two coset variables through the product of their representatives. Invariance
identifies the resulting summand on `Q(F) \ P(F)` with `φ_Q` times both cutoffs evaluated at the
same shifted minimal height. The finite-support proof justifies exchanging the sums over cosets
and the finite sums over parabolics. [Coset regrouping](ArthurTruncationCosets.md)

At each resulting `Q(F) \ P(F)` coset the coefficient of `φ_Q` is

\[
  \sum_{Q\subseteq R\subseteq P}
    (-1)^{\dim(\mathfrak a_Q^R)}\,\widehat\tau_Q^R(H)\,\tau_R^P(H).
\]

Here `dim(𝔞_Q^R)` is represented by `R.card - Q.card` on the simple-root index sets. The chamber
identity makes the coefficient zero for `Q ≠ P` and one for `Q = P`. The sole `P(F) \ P(F)` coset
therefore contributes `φ_P(x)`. Local boundedness and measurability of `φ` make its integral
converge on the compact unipotent quotient, by the compact representative argument in
`hasConstantTerm_of_locallyBoundedInvariant`. [Chamber identity](ArthurTruncationChambers.md)

## Full cancellation

Take the upper index to be all simple roots. The full parabolic rational subgroup is the whole
rational group by `parabolicRationalSubgroup_full_eq_top`. Transport finite support and the sum
along the resulting equivalence between the relative and full coset spaces. Partial truncation
is invariant under its rational upper parabolic, by right translation on its inner coset spaces,
so the evaluations at chosen representatives agree under transport. `constantTerm_full_eq`
identifies the final average with `φ(x)` because the full parabolic has trivial unipotent radical.
[Full-parabolic endpoint](ArthurTruncationCuspidal.md)

## Sources

- J. Arthur, *An introduction to the trace formula* (2005), §13, Proposition 13.3 and (13.10),
  printed pp. 73–74, PDF pp. 85–86. The regrouping follows the proof there, which applies (8.11)
  of §8, printed p. 46, PDF p. 58. Literature ID
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
  `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
- J. Arthur, *A trace formula for reductive groups I* (1978), §5 Lemma 5.1, printed p. 936,
  and §6 Lemma 6.3, printed pp. 940–941. The proof uses the Library’s qualitative full finiteness
  and the specialization of Langlands’ combinatorial lemma at the zero functional. Literature ID
  `arthur-1978-trace-formula-reductive-groups-I`, SHA-256
  `80ec482ea894e3af960e79cc1316ac2c2e806ad466f92c106650a59a0b2f17cc`.
