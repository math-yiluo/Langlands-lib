# Compression stability for sums with finite fixed-vector support

Worker 1751, using Worker 1755's same-exponent propagation interface. This is
an internal finite-maximum argument for the proposed qualitative VI.9.1 proof.
It does not establish the compact-level finiteness or componentwise eventual
stability used as hypotheses.

`FiniteFixedVectorSupport ρ H` is finiteness of the literal set of indices i
for which the actual fixed-vector module `fixedVectors (ρ i) H` is nontrivial.
It does not mean that only finitely many whole representations are nonzero, or
that the entire direct sum or any of its fixed spaces is finite dimensional.

`compressedAction_eventuallyStable_directSum_of_finite_support` assumes a
smoothness proof for each actual representation and its actual algebraic direct
sum, a compact open subgroup K, finiteness of this fixed-vector support, and
eventual stability of the actual compressed action on every component. It
concludes eventual stability of the actual compressed action on the sum. The
group, index and component-carrier universes remain independent; the direct-sum
carrier has the maximum of the index and component-carrier universes.

The implemented proof chooses a stationary threshold b(i) from each supplied
componentwise eventual-stability hypothesis. On the finite set S of indices
with nonzero K-fixed module, it takes B to be the maximum of 1 and the finite
supremum of those b(i). For an index in S, threshold monotonicity makes the
component stationary from B, hence its B-th compression power is stable. For an
index outside S, its fixed-vector module is a subsingleton, so both stability
equalities hold at every exponent. The same-exponent direct-sum
propagation then gives stability of the B-th power on the actual sum. Since
B is positive, this is eventual stability.

The source context is Renard 2026, VI.9.3, printed p.200 / PDF p.206, and
Appendix C.II, Lemma (iv), printed pp.276–278 / PDF pp.282–284. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Renard uses an already uniform quantitative bound in VI.9.3. The finite visible
support argument here is a derived alternative conditional passage and is not
attributed to that printed proof. The actual Bernstein/cuspidal decomposition,
fixed-level visibility, and generator-stability inputs remain separate work.
