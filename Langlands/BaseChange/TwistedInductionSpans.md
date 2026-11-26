# Subspaces of twisted distributions used in the pseudo-coefficient construction

The construction in Henniart–Lemaire (2011), II.5.10–II.5.13, uses a quotient
of the Grothendieck group of twisted representations. These internal,
derived definitions instead take complex linear spans of their actual
Library twisted distributions. This does not introduce a Grothendieck group
or assert an isomorphism with one. It amounts to working with the image of
the classes under twisted character evaluation.

- `twistedSpectrumSpan μ θ P` is the subspace of `Distribution G` spanned by
  the twisted distributions of irreducible admissible representations
  satisfying the supplied property `P`, with all choices of isomorphism
  `π ≅ π ∘ θ`. These are represented by their original actions on complex
  vector spaces of the specified carrier universe. The membership lemma
  `twistedDistribution_mem_twistedSpectrumSpan` just introduces a generator.
- `sigmaProperInducedSpan σ μ` is the subspace for `GL_n(E)` spanned by the
  twisted distributions of admissible inductions from all standard block
  parabolics with at least two blocks, with irreducible admissible inducing
  representation and its supplied `σ`-intertwiner. The ambient induction
  need not be irreducible. This is the Library's **unnormalized** smooth
  induction, and the twisting operator is the actual
  `TwistedPaleyWiener.inducedSigmaIntertwiner`. The generated span is not defined just using
  *ordered Langlands standard modules*. It also includes proper inductions
  of essentially tempered representations coming from parameters on a wall,
  which is relevant to II.5.13, proof, Case 2. The definition does not
  assert any disjointness, spanning or permutation of induction classes.
- `twistedDistribution_mem_sigmaProperInducedSpan_of_equiv` uses a
  representation equivalence from such an induction to an irreducible
  admissible `π`. Admissibility and irreducibility transport through that
  equivalence. Even if the equivalence does not match the chosen
  `σ`-intertwiners, `exists_twistedDistribution_eq_smul_of_equiv` expresses
  the twisted distribution of `π` as a scalar multiple of the generator.
  It therefore belongs to the span for any choice of `σ`-intertwiner of `π`.
- `exists_dual_agreeOn_of_disjoint` is pure linear algebra: when subspaces
  `L` and `N` are disjoint, a complex linear functional on `L` extends to a
  functional on the whole space vanishing on `N`. The composite `L → M → M/N`
  is injective. Transport the functional to the range, use Mathlib's
  `LinearMap.exists_extend` to extend on the quotient, then compose with
  the quotient map. No direct-sum decomposition of the whole space is
  needed.

The source definitions of twisted induction and the quotient relations
are in HL II.4.4 and II.5.2–II.5.5, and the construction in II.5.11 and
II.5.13, printed pp. 109–114. This module only supplies the subspaces and
the above linear-algebra and transport lemmas, not the structural results
about twisted standard modules in those sections.
