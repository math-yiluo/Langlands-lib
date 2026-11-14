# The singleton branch of Proposition 4.8

`Langlands.Global.Harris.Proposition48SingletonBranchStatement` is an
unproved implication for the final cyclic step when the actual Mackey
index has one element. The parent is one-place valid and `D/E` is an
actual cyclic Galois extension of prime degree in its normal closure.
For every automorphism representative the hypothesis supplies an actual
raw child, its inherited parent parity, exact Mackey rank, smaller
closure degree, a genuine base-character parity normalization, and
actual raw/corrected cuspidal realizations. Their relation is exactly
`IsUntwistedSolution`: raw weak induction, conjugate self-duality,
auxiliary supercuspidality, corrected regular algebraicity, and genuine
automorphic multiplication by the correcting character of `det`.
The raw realization is not assumed regular algebraic at its own rank.

The separate theorem premises are
`Harris1998Theorem12CuspidalStatement`,
`CuspidalSpectralRigidityStatement`,
`Proposition48IsobaricInvarianceStatement`, and
`CyclicStableDescentStatement`. The conclusion is the parent's full
four-part `HasSolution`, with its original inducing character. Number
fields are small; `uF` and `uV` are arbitrary.

Its proof must first transport the actual child to `D`, construct its
spectral attachments, and recover Galois stability from the restricted
monomial family using the invariance premise. The cyclic generator,
norm-kernel character and unitary realization needed by Arthur–Clozel
must be constructed. Arthur–Clozel then supplies the distinct actual
cuspidal descents, indexed by finite-character twists.

The remaining obligation is the argument of Lemma 1.6: prove the
required infinity type and local property for actual descents; obtain
conjugate self-duality up to a finite character; extend a character of
the real subfield and twist to a genuinely conjugate self-dual object;
apply Theorem 1.2; and use the irreducible restricted monomial family
to match its distinct extensions with the distinct descents. Select the
finite-character twist whose family is the induction of the parent's
original character, then establish its regular algebraicity, conjugate
self-duality and auxiliary supercuspidality. All correcting and
normalizing character transports are part of this obligation.

In particular, local descent at the unique auxiliary place must be
proved using the actual local base-change construction and its
supercuspidality reflection. Almost-everywhere weak base change alone
does not assert this ramified local identification. Theorem 1.7,
which assumes supercuspidality at the compared place, cannot supply
this step. The present branch implication does not assume a downstairs
supercuspidal component, a chosen compatible extension, or the desired
weak induction. The finite-character correction and selection are
conclusions to be constructed by its proof owner, not hidden fields in
a datum. This statement supplies their combined target; it does not
claim that the weak transfer predicate already includes them.

Source: M. Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), 177–210,
`harris-1998-local-langlands`, proof of Proposition 4.8, printed
pp.202–203 (one-based PDF pp.26–27), companion
`math_9611226v1.tex` lines 1574–1614 for the Mackey induction,
1630–1644 for invariance, and 1666–1674 for the singleton case and its
reference to Lemma 1.6. Lemma 1.6 and its proof are on printed
pp.188–189 (one-based PDF pp.12–13), companion lines 687–794;
the descent/extension matching is at 704–744 and finite-character
correction at 753–792. The half-integral twist Remark on printed p.191
is at companion lines 866–875.

The one-step, one-place and explicit parity-transport formulation is
derived from these passages. The statement neither proves the branch
nor strengthens the published Proposition 4.8 hypotheses. It changes
no published declaration and imposes no `n < p` condition.
