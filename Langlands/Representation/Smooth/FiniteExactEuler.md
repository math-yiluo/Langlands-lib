# Euler classes of actual finite exact sequences

This internal construction derives an Euler-class identity from actual exact
sequences in the published finite-length smooth representation category. It
uses the existing exact Grothendieck group and composition-factor map; its
provenance is the elementary short-exact-sequence telescoping argument below.
It assumes no irreducibility or effectivity assertion about an operator.

The coefficient field, group, and carrier universes are independent. A family
`C : ℕ → FiniteLengthObject k G` supplies actual smooth representations with
finite group-algebra length, and `d i : C i → C (i+1)` are actual equivariant
morphisms. Only degrees zero through `m` occur in the Euler sum. Exactness before
the terminal degree means that `d 0` is injective when `m > 0`, and that the
range of `d i` equals the kernel of `d (i+1)` whenever `i+1 < m`.

`boundary C d 0` is the actual zero subrepresentation of `C 0`; the successor
boundary is the actual invariant image of the preceding differential. The
canonical inclusions and actual range projections form short exact sequences
at the initial and internal degrees under precisely the hypotheses just
stated. `terminal C d 0` is `C 0`. At degree `i+1`, `terminal` is the actual
cokernel of `d i`, the quotient of `C (i+1)` by the incoming invariant range.
It has finite length because the actual quotient projection is surjective.
The incoming image, terminal term and this quotient always form a short exact
sequence. No splitting assumption is imposed.

`alternating_class` proves that the sum over `0 ≤ i ≤ m` of
`(-1)^i [C i]` equals `(-1)^m [terminal C d m]` in the exact Grothendieck
group. Its proof uses additivity for the actual image short exact sequences
and cancels successive incoming-image classes. `signed_alternating_class`
multiplies by the terminal sign, whose square is one. Finally,
`signed_alternating_effective` applies the published composition-factor map;
each coordinate of an actual finite-length class is a natural composition
multiplicity and is therefore nonnegative.

`signed_descending_class` also handles degree `i` corresponding to block length
`i+1`. For `m+1 ≤ n`, it proves that multiplying the sum of
`(-1)^(n-(i+1)) [C i]` by `(-1)^(n-(m+1))` gives the actual terminal class.
The proof checks the parity identity term by term and invokes
`signed_alternating_class`. Thus when the inducing block length is `b=m+1`,
`effective_of_descending_expansion` gives precisely the common sign
`(-1)^(n-b)` for any exact-K0 class supplied with this descending-sign expansion.
The expansion is an explicit equality hypothesis, not an assertion about a
particular operator. The effectivity proof uses only natural composition
multiplicities and does not import an Aubert irreducible-image statement or
preservation theorem.

These results retain every actual short exact relation, including nonsplit
relations. They neither construct Aubert differentials nor establish their
support exactness, and they do not assert that the full complex ending in zero
is exact. The surviving terminal quotient is retained explicitly. Applications
to a cut complex must still supply the actual terms and maps, the stated
injectivity and exactness, and the reindexing with the chosen unadjusted Aubert
operator. Rank-zero comparison is separate.

Worker 194 specified the terminal-cokernel interface; Worker 164 specified the
cut-degree indexing and the single-term case; Worker 585 implemented the
actual image sequences, telescoping proof and sign conversion.
