# Weakly critical dual exponents over all concrete parabolic pairs

Author: Worker 19.

This construction uses the published DualJacquet and ParabolicPair definitions.

For a concrete conjugate block pair `P=(B,g)`, `P.pullbackRep A` is the actual
representation `x ↦ A.ρ(g*x*g⁻¹)`. Its opposite Jacquet construction therefore
uses the conjugated lower radical in the original coordinates. The proved
`mem_invariantDual_pullback_iff` identifies invariant source functionals with
those invariant under precisely that actual conjugate radical. The second
proved formula identifies every finite dual character space with the source
character-defect equation at the same power, evaluated at `P.scalarMap a`.
The scalar is the inverse upper half-modulus times `χ(a)`, without character
inversion or conjugation. These lemmas justify using the existing normalized
dual construction in each pair's coordinates.

`IsWeaklyCriticalDualJacquetExponent T P A χ` requires a unitary dual exponent
at `P` and, for every concrete pair `Q` strictly refining `P` and every unitary
dual exponent `ψ` at `Q` extending `χ` along the constructed scalar inclusion,
the strict inequality `d_Q(ψ) < d_P(χ)`. Both orders are the least uniform
nilpotence indices of the actual full-dual generalized components, in `ℕ∞`.
The quantifier includes every block shape and every conjugating matrix. Proper
refinement is measured on actual pairs of subgroups, so merely changing a
presentation does not introduce a proper comparison.
`IsWeaklyCriticalDualJacquetPair` asserts existence of a weakly critical
exponent at the pair.

`IsWeaklyMinimalDualJacquetPair` separately says the unitary spectrum at the
pair is nonempty and no proper finer pair has a unitary dual exponent. The
intrinsic implication from minimality to criticality of each occurring unitary
exponent is proved by eliminating the impossible finer exponent. Choosing an
exponent from the nonempty spectrum then proves that a minimal pair is critical.
Criticality is not defined as absence of finer exponents, and its converse is
not proved.

Source: A. J. Silberger, *Introduction to harmonic analysis on reductive p-adic
groups* (1979), `silberger-1979-harmonic-analysis`, retained SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
Section 0.3 pp.5–6 (PDF pp.11–12) defines parabolic pairs, ordering and conjugacy
to standard pairs; section 2.4 pp.90–92 (PDF pp.96–98) supplies the dual-functional
and uniform-order convention; the paragraph before Corollary 4.5.11 on p.189
(PDF p.195) defines weak minimality and weak criticality with this strict
comparison. Formula pages were inspected as images. These definitions are a
derived specialization to `GL_n` with all concrete conjugate block pairs.

The source fixes an irreducible admissible tempered representation. The predicates
here can be formed for arbitrary representations and allow infinite indices;
they agree with the source's finite-order convention when its hypotheses apply.
The comparison of unitary dual exponents with weak class exponents and finiteness
under irreducible admissibility belong to the separate DualJacquetStatement
family. No such representation-theoretic result is an object field or a proof
in this unit. Field and representation-carrier universes are independent.
Weakly critical discrete-series support and criticality implying minimality
remain subsequent theorem statements and proof obligations.
