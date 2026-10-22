# Finite-level norms in an unramified finite free local algebra

This file states two finite-level arithmetic assertions and their complete
bundle. All three declarations are `Prop`-valued definitions; this contribution
does not formalize their proofs.

## Objects and hypotheses

The namespace is `Langlands.LocalClassField.UnramifiedAlgebra`. Let `R : Type u`
and `S : Type v` be commutative rings in independent universes. Write
\(m_R\) and \(m_S\) for their actual maximal ideals and \(N\) for the
determinant norm `Algebra.norm R : S →* R`.

The complete bundle `Statement.{u,v}` quantifies over:

- `[IsDomain R] [IsDiscreteValuationRing R]`, so \(R\) is a DVR and in
  particular a nontrivial local ring;
- `[IsLocalRing S]`, which already includes nontriviality of \(S\);
- `[Algebra R S] [IsLocalHom (algebraMap R S)]`;
- `[Module.Free R S] [Module.Finite R S]`;
- `[Finite (IsLocalRing.ResidueField R)]` and
  `[Finite (IsLocalRing.ResidueField S)]`, referring to the actual quotients by
  the maximal ideals.

Its remaining hypothesis is exactly

\[
  \operatorname{Ideal.map}(\operatorname{algebraMap} R S)(m_R)=m_S.
\]

No domain or DVR assumption on \(S\) is added. The finite free multiplication
matrices and the displayed equality suffice for the argument described below.
There is no assumed surjectivity of the norm, residue norm, or residue trace;
there is no Galois, completeness, topology, or class field theory assumption.

## Individual propositions and complete bundle

`NormPreservesUnitCongruences R S` means

\[
  \forall n\in\mathbb N,\ \forall x\in S^\times,\quad
  x-1\in m_S^n\ \Longrightarrow\ N(x)-1\in m_R^n.
\]

`NormApproximatesUnitCongruences R S` means

\[
  \forall n\in\mathbb N,\ \forall y\in R^\times,\quad
  y-1\in m_R^n\ \Longrightarrow\
  \exists x\in S^\times,\quad
  x-1\in m_S^n\ \land\
  y\,N(x)^{-1}-1\in m_R^{n+1}.
\]

In the second formula, \(N(x)\) is the unit
`Units.map (Algebra.norm R) x`, the product and inverse are formed in `Rˣ`,
and then the result is coerced to \(R\) before subtracting \(1\).
Both formulas use literal ideal powers and ideal membership.

The individual declarations define properties for any local commutative
`R`-algebra `S`; they do not claim those properties always hold.
`Statement` universally quantifies the full structural hypotheses above and
asserts their conjunction under the mapped-maximal-ideal equality. This is the
single complete target for a subsequent exact proof.

Every natural level is included. At \(n=0\), \(m_R^0=R\) and \(m_S^0=S\), so
the input congruences are vacuous and preservation is automatic.
Approximation at that level asks for a unit \(x\) with
\(yN(x)^{-1}\equiv1\pmod {m_R}\).
No assertion of full unit-norm surjectivity is included.

## Source and mathematical justification

The original source read for this contribution is Jean-Pierre Serre,
*Local Fields*, Marvin Jay Greenberg translation, GTM 67, Springer (1979),
Chapter V, §2, Propositions 1–3, the following remarks, and the non-Galois
exercise, printed pp.81–82 (PDF pp.88–89).
The registered source is `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`,
SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Serre's Proposition 1 gives preservation of unit levels for unramified local
field extensions. Proposition 2 identifies the induced map at level zero with
the residue norm, and at positive levels with the residue trace tensored with
the one-dimensional base graded piece. Proposition 3 uses the surjectivity of
separable residue trace and a completeness argument to obtain stronger
surjectivity results. The following remark covers finite residue norm
surjectivity, and the exercise asks for the non-Galois extension.

The present finite free local-algebra formulation is a derived
matrix-theoretic generalization of the finite-level calculation, not a literal
quotation of Serre's theorem. Its justification does not use the
completeness step:

1. Choose a uniformizer \(\pi\) of \(R\). The mapped-maximal-ideal equality
   gives \(m_S^n=\pi^n S\) for every \(n\), where \(\pi\) acts through the
   algebra map. For \(n\geq1\), write \(x=1+\pi^n a\). The determinant
   expansion gives, for some \(r\in R\),
   \[
     N(1+\pi^n a)
        =1+\pi^n\operatorname{Tr}_{S/R}(a)+r\pi^{2n}.
   \]
   This proves preservation and gives the first-order norm formula modulo
   \(m_R^{n+1}\), since \(2n\geq n+1\).
2. Reducing a finite free basis modulo \(m_R\) identifies the quotient
   multiplication matrices. Thus norm and trace reduce to norm and trace
   on \(S/(m_R S)=S/m_S\) over \(R/m_R\). These are the actual residue fields.
   Their induced extension is finite and separable because they are finite
   fields. Consequently its trace is surjective.
3. For \(n\geq1\), write \(y=1+\pi^n b\), choose a residue trace preimage
   of the residue class of \(b\), and lift it to \(a\in S\).
   Then \(x=1+\pi^n a\) is a unit because \(\pi^n a\in m_S\), and the
   expansion gives \(N(x)\equiv y\pmod {m_R^{n+1}}\).
   Multiplying \(y-N(x)\) by the inverse of the unit \(N(x)\) gives exactly
   the stated multiplicative correction.
4. At \(n=0\), use surjectivity of the norm between the finite residue-field
   unit groups. A nonzero residue preimage lifts to a unit of the local
   ring \(S\). Compatibility of determinant norm with reduction gives the
   requested correction modulo \(m_R\).

These are mathematical justifications for the statement's scope. The
associated Lean file contains only proposition definitions; none of these
proof steps is claimed to have been implemented there. Full norm
surjectivity requires a separate lifting theorem with topological hypotheses.

## Pinned Mathlib audit and later proof interface

The following sources were inspected in Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, with Lean 4.34.0:

- `RingTheory/Norm/Defs.lean`: `Algebra.norm_eq_matrix_det` identifies the
  actual norm with a multiplication-matrix determinant.
- `RingTheory/NormTrace.lean`: `Algebra.norm_one_add_smul` gives exactly
  the first-order expansion above for finite free algebras over commutative
  rings, without a domain or Galois hypothesis on the target.
- `RingTheory/Trace/Quotient.lean`: `Algebra.trace_quotient_mk` compares
  the trace modulo the maximal ideal with the trace on the quotient algebra,
  using `Module.basisQuotient` and its coordinate formula.
- `RingTheory/Trace/Basic.lean`: `Algebra.trace_surjective` supplies
  surjectivity for finite separable field extensions.
- `FieldTheory/Finite/GaloisField.lean`:
  `FiniteField.unitsMap_norm_surjective` supplies the finite residue-field
  unit-norm result. Galois properties of finite fields may be derived inside
  this argument; they are not hypotheses on the original rings.
- `RingTheory/DiscreteValuationRing/Basic.lean` supplies the local-ring
  instance for a DVR and the existence of an irreducible uniformizer;
  `RingTheory/LocalRing/ResidueField/Defs.lean` defines the actual residue
  fields.

The analogous norm-under-quotient comparison still needs to be supplied in
the later proof, for example by the same quotient-basis multiplication
matrices and determinant compatibility with ring homomorphisms. The audit
identifies ingredients and does not assert that Mathlib already proves this
bundle. Later arithmetic applications must also establish the finite free
local algebra and mapped-maximal-ideal hypotheses, and compare this ring
norm with any fraction-field norm they use.
