# Splitting over a finite étale diagonalizable quotient

Module
`Langlands.GroupScheme.Trigonalizable.EtaleExtensionSplitProof`.

`Langlands.GroupScheme.etaleDiagonalizableExtensionSplit` proves the
unchanged [`EtaleDiagonalizableExtensionSplitStatement.{u}`](EtaleExtensionSplitStatement.md)
in every universe. For the given fppf quotient `q : G ⟶ D(Λ)` by a
smooth connected unipotent subgroup over a perfect field, it produces a
`k`-group-scheme section `s`, with `s ≫ q = 𝟙 D(Λ)`.

## Implemented proof

Split by the characteristic exponent `p`:

- **Characteristic zero (`p = 1`).** Use
  `TrigonalizableExtensionSplit.admitsTower` for the given quotient and
  `TrigonalizableExtensionSplit.oneStepSplitting_of_charZero` for its
  steps. The tower splitting lemma
  `TrigonalizableExtensionSplit.exists_section_of_admitsTower'` gives
  the section. This branch uses the published tower and one-step
  results, not the reduction of the full trigonalizable extension theorem
  to the present statement.
- **Positive characteristic.** Coprimality of `Nat.card Λ` with `p`
  implies `Λ` has no nonzero `p`-torsion: the order of such an element
  divides both `Nat.card Λ` and `p`. The published diagonalizable
  smoothness criterion gives smoothness of `D(Λ)`. Its coordinate ring
  `k[Λ]` is reduced by `Diagonalizable.SmoothConnectedCriteria.isReduced_of_smooth`
  and finite-dimensional by its finite group-algebra basis. It is thus
  a reduced Artinian ring, a finite product of residue fields. These
  fields are separable over the perfect ground field, so the coordinate
  ring and `D(Λ)` are étale. Over `L = SeparableClosure k`,
  `EtaleMultiplicativeTypeOrder.forward` for the diagonalizable group
  (in particular of multiplicative type) supplies the prime-to-`p`
  order of `D(Λ)(L)`.

  Smoothness of the supplied represented kernel implies smoothness of
  the fppf quotient `q`, so `G` is smooth as well. The quotient's
  `kernelIso` transfers connectedness and unipotence from the supplied
  subgroup to `kernel q`. Now apply the
  [dimension induction](EtaleExtensionDevissage.md) to reduce to vector
  kernels over the same quotient. The
  [vector step](EtaleVectorExtension.md) splits each such extension by
  torsor triviality, averaging over the finite geometric point group,
  and descent back to a homomorphism over `k`.

## Source and scope

M. Raynaud, SGA 3 Exposé XVII, Gille–Polo recomposed edition (November
2008), `sga3-expose-xvii-gille-polo-2008`, SHA-256
`687f333c4f86221e7898f44c1706845d8e0b79af50ab31f3ed9a3b0f696ae25b`:
Théorème 5.1.1 (printed p.345, PDF p.21) fixes the notation and meaning
of a trivial extension; Lemme 5.2.3 i) c) (printed pp.346–347, PDF
pp.22–23) is the target's source. The target is its specialization to
finite étale diagonalizable quotient and smooth kernel. In positive
characteristic the proof retains the source's scheme-section and
averaging ideas (Lemmes 5.2.1 c), 5.2.4, and Corollaire 5.2.4 bis,
printed pp.346–348, PDF pp.22–24), but uses stable central vector groups
instead of a characteristic series with commutative factors. It averages
the factor set directly, not by a general cohomology-vanishing theorem.
No reduction of a nonsmooth kernel is needed. The proof makes no claim
about conjugacy of sections, or about the full SGA 3 lemma in its broader
scope.
