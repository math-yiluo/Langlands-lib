# Properness of homogeneous quotients by parabolic subgroups

Module `Langlands.GroupScheme.ParabolicQuotientProperProof`.

The theorem `Langlands.GroupScheme.parabolicSubgroupQuotientProper` proves
`ParabolicSubgroupQuotientProperStatement.{u}` (module
`Langlands.GroupScheme.HomogeneousQuotientStatement`) for an arbitrary universe `u`. Let `k` be a
field and `G` a connected smooth affine group scheme over `Spec k`. Let `i : P ⟶ G` be parabolic
in the published geometric sense `IsParabolicSubgroup`. Let `q : G.X ⟶ Q` be any homogeneous
quotient by `range i`. Here `Q` is separated, locally of finite type and quasi-compact over `k`,
and `q` is smooth, surjective and quasi-compact. Its fibres on `T`-points are exactly the cosets
`g · range i`, that is, `g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ range i`. Then `Q` is proper over `k`.

This is the "if" direction of Milne, *Algebraic Groups* (2017), Theorem 17.16 (printed p. 356 / PDF p. 372).

The proof is one application of the reduction
`Langlands.GroupScheme.ParabolicQuotient.parabolicSubgroupQuotientProper_of` (module
`Langlands.GroupScheme.ParabolicQuotientProperReduction`, documented in its own Markdown file).
That reduction takes three hypotheses, and each is supplied by a published theorem:

- `SomeBorelQuotientProperStatement`: `Langlands.GroupScheme.someBorelQuotientProper` (module
  `Langlands.GroupScheme.Absolute.BorelProperQuotientProof`). Over an algebraically closed field,
  some Borel subgroup has proper homogeneous quotients.
- `BorelConjugacyStatement`: `Langlands.GroupScheme.borelConjugacy` (module
  `Langlands.GroupScheme.Absolute.BorelConjugacyProof`). The reduction uses only its second
  conjunct, that any two Borel subgroups over an algebraically closed field are conjugate by a
  rational point.
- `SmoothSubgroupQuotientExistenceStatement`: `Langlands.GroupScheme.smoothSubgroupQuotientExistence`
  (module `Langlands.GroupScheme.HomogeneousQuotientProof`). Smooth closed subgroups have
  homogeneous quotients. It is used only to build a quotient by the fixed Borel subgroup over
  `k̄`.

The theorem keeps the published statement as it is. It quantifies over the same model `Q` and
projection `q`, and it adds no premise.
