# Admissibility of irreducible automorphic subquotients from admissibility of generated realizations

Lean module: `Langlands.Automorphic.IrreducibleSubquotientAdmissibilityReduction`.
It imports `Langlands.Automorphic.AutomorphicAdmissibilityStatement` (the
statements), `Langlands.Automorphic.OperatorCompactCompletion`
(for the faithful function realization and continuity of its point evaluations),
`Langlands.Representation.CompactMaschke` (for
`CompactMaschke.exists_lift_intertwiner`) and
`Langlands.Representation.Compact.ProjectionProof` (for the averaging lemmas
on `Compact.averageMap`).

This module is a helper for the proof of
`Langlands.Automorphic.IrreducibleSubquotientAdmissibilityStatement`.
It proves the implication from `GeneratedFormAdmissibilityStatement`. It does
so by constructing a cyclic realization and transferring joint admissibility
along its quotient map. The entry module applies this implication to the
published proof of `GeneratedFormAdmissibilityStatement`.
[Exact proof](IrreducibleSubquotientAdmissibilityProof.md)

## Main theorem

```lean
theorem Langlands.Automorphic.irreducibleSubquotientAdmissibility_of_generatedFormAdmissibility
    (h : GeneratedFormAdmissibilityStatement.{u}) :
    IrreducibleSubquotientAdmissibilityStatement.{u}
```

Both statements are published in
`Langlands/Automorphic/AutomorphicAdmissibilityStatement.lean`.

- `GeneratedFormAdmissibilityStatement` (Borel–Jacquet Proposition 4.5
  (1) ⇒ (4)): for every number field `F`, every `n` and every automorphic form
  `f` on `GL_n` over `F`, the realization `generatedFormOperatorRealization F n f`
  is jointly admissible (`OperatorRealization.IsJointlyAdmissible`).
- `IrreducibleSubquotientAdmissibilityStatement` (Borel–Jacquet §4.6): for
  every number field `F`, every `n` and every `Q : OperatorSubquotient F n` with
  `Q.IsIrreducible`, `Q.IsJointlyAdmissible`.

Joint admissibility is the Hom form of the Library
(`Langlands.IsJointlyAdmissible`, `UnitaryContragredientCriterion.lean`): for
every open subgroup `L` of `GL_n(𝔸_f)` and every representation `σ` of the
standard compact subgroup `K_∞` on `Fin m → ℂ`, the space
`jointMultiplicitySpace ρ κ L σ` of `K_∞`-equivariant linear maps from `σ` into
the `L`-fixed vectors is finite-dimensional. Here `σ` need not be continuous or
irreducible, and `L` need not be compact.

The theorem keeps the universe `u` of the number field.

## Other declarations

### Generic lemmas (namespace `Langlands`)

- `jointMultiplicitySpace_mono`: if `L' ≤ L`, then
  `jointMultiplicitySpace ρ κ L σ ≤ jointMultiplicitySpace ρ κ L' σ`. An
  `L`-fixed vector is `L'`-fixed.
- `isJointlyAdmissible_of_surjective` (**quotients of jointly admissible
  pairs**). Let `G` be a topological group in which every open subgroup
  contains a compact open subgroup, and `K` a compact group. Let `ρ` (smooth)
  and `κ` be commuting representations of `G` and `K` on `V`. Assume that every
  vector of `V` lies in a finite-dimensional `κ`-stable subspace, and that
  `k ↦ μ (κ k x)` is continuous for every linear form `μ` and every `x`. Let
  `p : V → W` be a surjective linear map that intertwines `ρ, κ` with
  representations `ρ'` (smooth) and `κ'` on `W`. If `(ρ, κ)` is jointly
  admissible, so is `(ρ', κ')`.

  Proof. Fix an open `L`, `m` and `σ`. Choose a compact open `L₀ ≤ L`. By
  `jointMultiplicitySpace_mono` it suffices to show that the multiplicity space
  of `W` for `L₀` lies in the image of the multiplicity space of `V` for `L₀`
  under composition with `p`. The latter is finite-dimensional by hypothesis.
  Let `φ : (Fin m → ℂ) → W` be `K`-equivariant with `L₀`-fixed values.
  1. *Lifting the `K`-equivariance.* Write `σ` as a homomorphism
     `τ : K →* Matrix (Fin m) (Fin m) ℂ` (through
     `LinearMap.toMatrixAlgEquiv'`; `σ k x = τ k *ᵥ x`). The Library's
     `CompactMaschke.exists_lift_intertwiner` (`CompactMaschke.lean`) gives a
     `K`-equivariant `ψ : (Fin m → ℂ) → V` with `p ∘ ψ = φ`. Its hypotheses are
     the finiteness and weak continuity assumptions on `κ`, the equivariance of
     `p`, and the surjectivity of `p`, which puts the values of `φ` in the range
     of `p`.
  2. *Averaging over `L₀`.* Let `A = Compact.averageMap ρ hρ L₀` and
     `A' = Compact.averageMap ρ' hρ' L₀` be the averaging operators of the
     smooth representations over the compact open subgroup `L₀`
     (`Langlands/Representation/Compact/Definitions.lean`). `A` has values in
     the `L₀`-fixed vectors (`averageMap_mem_fixedVectors`). It commutes with
     every `κ k`, and `p ∘ A = A' ∘ p`, by `averageMap_commute`
     (`Compact/ProjectionProof.lean`) applied to the intertwiners `κ k` (which
     commute with `ρ`) and `p`. `A'` fixes the `L₀`-fixed vectors of `W`
     (`averageMap_id`).
  3. So `A ∘ ψ` is `K`-equivariant with `L₀`-fixed values, and
     `p ∘ A ∘ ψ = A' ∘ φ = φ`.

### Operator realizations and subquotients (namespace `Langlands.Automorphic`)

- `OperatorRealization.continuous_dual_compactOrbit` supplies weak continuity of each compact orbit. On the finite-dimensional orbit span, the proof expresses the restriction of a linear functional using point evaluations.
- `OperatorRealization.exists_compactStable_finiteDimensional`: every vector
  of an operator realization lies in a finite-dimensional subspace stable under
  `K_∞`, namely the span of its `K_∞`-orbit. It is finite-dimensional by the
  published `compactRepresentation_isFiniteVector`.
- `OperatorSubquotient.isJointlyAdmissible_of_surjective`: if `S` is a jointly
  admissible operator realization and `p` is a surjective intertwiner of the
  whole operator algebra from `S.representation` to `Q.representation`, then
  `Q` is jointly admissible. This applies `isJointlyAdmissible_of_surjective`
  with `G = GL_n(𝔸_f)`, `K = K_∞`, `ρ = S.finiteRepresentation`,
  `κ = S.compactRepresentation`. The inputs are published lemmas:
  `finiteRepresentation_isSmooth` for `S` and `Q`,
  `finiteRepresentation_compactRepresentation` (the two actions commute),
  `OperatorRealization.exists_compact_openSubgroup_le` (compact open
  subgroups), and the intertwining property of `p` on the finite adelic and
  compact operators. The local compact-orbit continuity proof supplies the
  weak continuity hypothesis.
- `OperatorSubquotient.generatedProjection Q S h`: for `h : S ≤ Q.upper`, the
  inclusion of `S` into `Q.upper` followed by `Q.projection`, as an intertwiner
  of the whole operator algebra. `generatedProjection_apply` computes it.
- `OperatorSubquotient.exists_generatedForm_surjective` (**a cyclic vector**):
  if `Q.IsIrreducible`, there are an automorphic form `f` and a surjective
  intertwiner from `(generatedFormOperatorRealization F n f).representation` to
  `Q.representation`.

  Proof. `Q.Space` is nonzero: its module over the operator monoid algebra is
  simple. Choose `w ≠ 0` in `Q.Space` and `x ∈ Q.upper` projecting to `w`
  (`projection_surjective`). Let `f` be the automorphic form underlying `x`
  (`stableAutomorphicEquiv`). The published
  `generatedFormOperatorRealization_le_iff` and `mem_fullFormImage_iff` give
  `generatedFormOperatorRealization F n f ≤ Q.upper`, and
  `mem_generatedOperatorRealization` gives that `x` lies in the generated
  realization. By Mathlib's `Representation.IsIrreducible.surjective_or_eq_zero`
  the intertwiner `generatedProjection` into the irreducible `Q.representation`
  is surjective or zero. It is not zero, because it sends `x` to `w`.

## Proof of the main theorem

Let `Q` be an irreducible operator subquotient. By
`exists_generatedForm_surjective` there are `f` and a surjective intertwiner
`p` from the realization generated by `f` onto `Q`. By
`GeneratedFormAdmissibilityStatement` that realization is jointly admissible.
`OperatorSubquotient.isJointlyAdmissible_of_surjective` transfers this to `Q`.

## Sources and provenance

- A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*,
  Proc. Sympos. Pure Math. 33, Part 1 (Corvallis 1977), Amer. Math. Soc., 1979,
  pp. 189–202. Registered source `borel-jacquet-1979-automorphic`
  (Corvallis Part I file
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`,
  SHA256
  `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`; printed
  page = PDF page + 5).
  - Proposition 4.5, p.196 (PDF 191): for a smooth function `f` on `G(𝔸)`
    satisfying 4.2 (a), (b), (d), (1) "`f` is an automorphic form" implies
    (4) "The space `f * ℋ` is an admissible `ℋ`-module". This is
    `GeneratedFormAdmissibilityStatement`.
  - §4.6, p.196 (PDF 191): "An irreducible representation of `ℋ` is automorphic
    (resp. cuspidal) if it is isomorphic to a subquotient of a representation
    of `ℋ` in the space of automorphic (resp. cusp) forms on `G(𝔸)`. It
    follows from 4.5 that such a representation is always admissible." This is
    `IrreducibleSubquotientAdmissibilityStatement`.

The main theorem is Borel–Jacquet's "It follows from 4.5" for `G = GL_n` over
a number field, in the formalization of the statement module. Its Markdown,
§§4–5 and §9, explains the choices (operator subquotients for automorphic
representations, `generatedFormOperatorRealization` for `f * ℋ`, the Hom form of
admissibility).

Borel–Jacquet give no details. The proof follows the outline of §7, item 3, of
the statement Markdown: a cyclic vector, then the
passage of joint admissibility to a quotient, with a reduction to compact open
`L`. It differs from that outline in two points.

- The `K_∞`-types are not handled by isotypic projections. Instead, a
  `K_∞`-equivariant map from `σ` into the quotient is lifted to the whole space
  by the published compact Maschke lifting lemma
  `CompactMaschke.exists_lift_intertwiner` (the standard averaging
  proof of complete reducibility of finite-dimensional continuous
  representations of compact groups, see `CompactMaschke.md`).
- The `L`-fixed vectors are lifted by the published averaging operator
  `Compact.averageMap` over the compact open subgroup `L₀`, applied after the
  lift. An average over a finite quotient `L₀ / L'` is the same device: the
  Library's `averageMap` takes the mean over the finite `L₀`-orbit of a vector.

The comparison of a realization with the subquotient
`OperatorRealization.toSubquotient` is not needed.
The transfer works directly with the surjective intertwiner from the realization
onto `Q`.

## What is not asserted

- Any converse: admissibility of a subquotient is not shown to imply anything
  about the realization it comes from.
- Anything about reducible subquotients. The quotient lemma holds for any
  surjective intertwiner, but the cyclic vector argument uses irreducibility.

## Lean checks

A compilation check of the module reported no errors or warnings. The main theorem depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.
