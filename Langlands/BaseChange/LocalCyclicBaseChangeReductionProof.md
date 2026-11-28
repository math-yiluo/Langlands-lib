# Weak cyclic base change from σ-lifts

The theorem `Langlands.BaseChange.localCyclicBaseChangeReduction` proves
`Langlands.BaseChange.LocalCyclicBaseChangeReductionStatement.{uK,uV}`. The seven σ-lift
propositions are the hypotheses of the implication. The conductor argument uses
`Langlands.BushnellKutzko.supercuspidalConductorRankLowerBound` to bound the first fixed
level below by the rank for supercuspidal classes of rank two or higher.

## Cyclic steps and supports

The Galois group of a step `S` has prime order equal to `S.degree`. A generator `σ` fixes
exactly the base field, and `powersEquiv` enumerates the group by the powers of `σ` with
exponent less than the degree. The fields use their canonical p-adic topologies. The
module-topology comparison applies to the algebra induced by `S.embedding`.

For each supercuspidal class, choose a representative and apply the discrete-series
existence premise to its essentially square-integrable action. Apply the structure
premise to the lift to obtain a block and its period `s`. Define the output to be the
multiset of the `s` conjugate block classes with their ranks, using the ordering by powers
of `σ`. The ranks add up to the original rank. For `s = 1` all Galois conjugates of the
block are isomorphic. For `s = S.degree` the full orbit multiset is invariant by
reindexing the Galois group through right multiplication. This gives (W1).

The normalized orbit product has the multiset above as a supercuspidal support in
Zelevinsky's sense. An equivalence of two such irreducible products identifies their
supports by `AllFieldBZ.glSupercuspidalSupportUniqueness`. Conversely, an equality of
multisets gives the same number of blocks and the same block rank. Matching occurrences
gives a permutation of the ordered blocks. The equivalence of irreducible induced
products under this permutation and the blockwise equivalences identify the two
products. Matrix reindexing along the equality of total ranks transports these
comparisons to the original lifts.

## Twists, fibres, and image

The open-kernel theorem for norm-trivial homomorphisms identifies the ordinary norm
character group with the continuous quasi-characters in `S.normCharacters`. Its order
is `S.degree`. Twisting by such a character on the base side leaves the upstairs
action after norm pullback equal to the original one. Transport of the intertwiner along
that equality preserves its underlying linear map. The twist and uniqueness premises
identify the two lift classes, so their support multisets agree. This gives (W2).

If two output multisets agree, the product comparison identifies their lifts. Transport
both lift identities to the same upstairs action and apply the fibre premise. The two
base classes then differ by a norm twist. The class stabilizer is the one measured by
`normTwistStabilizer` on the representative. With trivial stabilizer it has size one, so
the support is a singleton and (W2) gives the other fibre inclusion in (W3a). With full
stabilizer its size is the extension degree. The period condition gives a free Galois
orbit at the divided rank, and the base class is the only one in its fibre. This proves
(W3b).

In (W3c) the converse premise applies with period one for an invariant block and with
period `S.degree` for a block with trivial Galois stabilizer. The induced action can
have carrier universe `max uK uV`. The theorem
`padicIrreducibleSmoothSmallRealization` gives an equivalent action in `Type uV`.
Transport of admissibility and the σ-lift identity allows uniqueness to be applied at
the exact carrier universes of the implication. Support uniqueness identifies this
output with the required singleton or full orbit.

## Conductors

The extension residue-cardinality formula gives `IsResidueDegree` for `S.residueDegree`.
The different-existence theorem gives a trace-codifferent exponent whose power of the
maximal ideal is the actual different ideal. The powers of the maximal ideal are strictly decreasing, so this
exponent equals the infimum in `S.differentExponent`.

Normalized level existence and the supercuspidal Swan formula give a finite first fixed
level. Therefore the seventh premise gives the natural-number identity

\[
\sum_{\eta\in\Xi} a(\eta\pi)=f\bigl(s\,a(B)+nd\bigr).
\]

Here \(B\) is the chosen block, \(n=s m\) is the base rank with block rank \(m\),
\(\Xi\) is the group of norm characters, and \(f,d\) are the residue degree and different
exponent. Galois conjugation preserves the conductor of \(B\). The proof handles the
truncated subtraction in (W4) through
\((a-n)_+=a-n+(n-a)_+\), using integer arithmetic for the right-hand side.

For \(n>1\) the terms \((n-a(\eta\pi))_+\) vanish by the higher-rank lower bound. For a
block of rank greater than one the same lower bound kills its correction. A rank-one
block in total rank greater than one belongs to a free Galois orbit. Every rank-one
class of conductor zero is an unramified character and hence fixed by all Galois
automorphisms, so this block has conductor at least one.

For \(n=1\) the orbit period and block rank are both one. Identify the base and the
block with rank-one quasi-characters. The one-block equivalence identifies the block
with the lift, whose character is the norm pullback by
`charZeroRankOneSigmaLiftNormPullback`. The rank-one Euler polynomial has degree one
at conductor zero and degree zero at positive conductor. Taking degrees in
`prod_lPolynomial_normTwists` therefore counts the unramified norm twists. The count is
\(f\) when the lifted character is unramified and zero otherwise. This is exactly the
correction for replacing signed differences by truncated differences at rank one.

Combining the conductor identity, the correction identity, \(|\Xi|=ef\), and
\(n=sm\) proves (W4) with wild different exponent \(d-e+1\).

## Certification for a chosen generator

For a cyclic step `S` and a generator `σ`, the theorem
`exists_weakCyclicBaseChange_sigmaLiftOnSupercuspidals` gives one map `Ch` that satisfies
both `IsWeakCyclicBaseChange S Ch` and `IsSigmaLiftOnSupercuspidals S.embedding Ch σ`.
The construction retains the orbit presentation used to define each `Ch k π`.

Let `A` represent `π`, and let `A₀` be the chosen representative. Its lift `L`
is equivalent to the orbit product of its block `B`. Use that orbit product at rank
`k + 1` for the certifying representation, with carrier in `Type (max uK uV)`.
Transport the admissibility and intertwiner from `L` along the equivalence.
Then `IsSigmaLift.transport` moves the character identity from `A₀` to `A`
and from `L` to the orbit product. The generator equation gives
`orderOf σ = S.degree`.

For supercuspidal support, `sigmaOrbitProduct_equiv_canonical` unfolds the two
normalized inductions to `normalizedInducedOf` with equal half-modulus characters.
The canonical p-adic product induction of the conjugate blocks therefore contains the
orbit product as a subrepresentation. Its block classes, read through
`supercuspidalSupportDatum`, give the support `Ch k π`. Choosing a generator and
retaining the weak cyclic base-change property gives the reduction theorem.

## Sources

- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour
  GL_n en caractéristique non nulle*, Mém. Soc. Math. Fr. 124 (2011). Registered source
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, SHA-256
  `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
  II.1.3, II.2.9 Remarks (2) and (4), II.4.6–II.4.8, and II.4.12 give the lift
  conventions, uniqueness, twisting, existence, fibre and orbit-product statements.
- J. Arthur and L. Clozel, *Simple algebras, base change, and the advanced theory of
  the trace formula*, Ann. of Math. Studies 120 (1989). Registered source
  `arthur-clozel-1989-base-change`, SHA-256
  `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
  Chapter 1, Proposition 6.9(ii), printed pp. 60–61, supplies the epsilon identity
  behind the conductor premise. The rank-one Euler comparison uses the denominator
  form of the norm-factor identity.
- *The numerical local Langlands correspondence for GL_n*, registered source
  `operator-numerical-llc-route-2026-11-16`, file `numerical-LLC-route.tex`, SHA-256
  `b57ba9428a0d664d0c6beed75bbc2a2d0d73638718a8080c2f913b75acbbb3c8`.
  Section 6.4, Theorem `thm:BC`, and §7.1 item 6 describe the base-change clauses
  and their use in the numerical descent.
