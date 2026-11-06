# Derived subgroups of the preimage of a subgroup in a central cover

Author: Worker 1413.

Module `Langlands.GroupScheme.SimplyConnected.CoverPreimageDerived`,
namespace `Langlands.GroupScheme.CoverPreimage`. Internal helpers for clause 5
of the reduction
[`SplitTorusCentralizerCoverPreimageReduction`](SplitTorusCentralizerCoverPreimageReduction.md).
They introduce no literature assertion. Notation as in
[`CoverPreimageCharacters`](CoverPreimageCharacters.md).

## General lemmas

- `flatSurjectiveProperty` abbreviates `@Flat ⊓ @Surjective`. It is used to
  apply Mathlib's `MorphismProperty.pullbackMap` to products of morphisms.
- `commutator_central_mul`: in a group, central factors drop out of a
  commutator: `⁅a b, c d⁆ = ⁅b, d⁆` when `a` and `c` are central.
- `range_derived_comp_le`. For any homomorphism `φ : H ⟶ G` and derived
  subgroups `dH`, `dG`, the range of `dH ≫ φ` lies in the range of `dG`. The
  inverse image of the derived subgroup of `G` is represented by the closed
  subgroup `subgroupIntersectionFst φ dG` (published
  `IsRepresentedBy.comap_subgroupIntersectionFst`). It contains every
  commutator of `H`, so it contains the derived subgroup of `H` (published
  `IsDerivedSubgroup.range_le`).

## Over a field

- `isIntegral_of_smooth_connected`: a smooth connected affine group over a
  field is integral. `nonempty_groupScheme`: a group scheme over a field has
  a point (its unit).
- `isCentralIsogeny_of_comp`. Let `CM`, `D'`, `DM` be smooth affine groups
  with `CM` and `D'` connected. If `q : D' ⟶ DM` and `a ≫ q` are central
  isogenies, then so is `a : CM ⟶ D'`.
  - *Kernel.* A point killed by `a` is killed by `a ≫ q`, so it is central.
  - *Finiteness.* `a` is finite because `a ≫ q` is finite and `q` is
    separated.
  - *Surjectivity.* The published `HomImage.exists_image` factors `a` through
    a closed subgroup `I ⊆ D'`. The composite `I ⟶ D' ⟶ DM` is surjective
    onto the reduced `DM`, hence schematically dominant. `D'` is integral and
    finite over `DM`, so the published `isIso_of_closedImmersion_finite_comp_schematic`
    (module `Torus.FiniteHomRigidity`) makes `I ⟶ D'` an isomorphism.
  - *Flatness.* Flatness and local finite presentation then come from the
    factorization.
- `isCentralIsogeny_derivedLift`. Assume: `G` connected reductive with
  derived subgroup `d`; `π` a central isogeny; `i : Z ⟶ G` central with
  `centralProduct i d` a central fppf cover; `j : M ⟶ G` closed with
  `iM ≫ j = i`; `M` and `M'` connected reductive; `dM : DM ⟶ M` and
  `d' : D' ⟶ M'` derived subgroups. Let `q : D' ⟶ DM` be the factorization
  of `d' ≫ p` through `dM` (published `IsRepresentedBy.liftOfLE` with
  `range_derived_comp_le`). Then `q` is a central isogeny.
  - *Finiteness.* `p` is a base change of the finite map `π ≫ d`, so
    `d' ≫ p = q ≫ dM` is finite, hence so is `q`.
  - *Surjectivity.* `HomImage.exists_image` factors `q` through a closed
    subgroup `I ⊆ DM`. Let `Ψ : Z × M' ⟶ M` be `toDerivedPart` (on the second
    factor) followed by the restricted product. On points `Ψ(z, c) = iM(z) p(c)`,
    and `Ψ` is flat and surjective. So `Ψ × Ψ` is flat, surjective and
    schematically dominant onto the reduced `M × M`. After `Ψ × Ψ`, the
    commutator morphism of `M` equals `p` applied to a commutator of `M'`
    (`commutator_central_mul`). That commutator factors through `d'`. So the
    commutator morphism of `M` factors through the closed immersion `I ⟶ M`
    (published `exists_lift_of_isSchemeTheoreticallyDominant`). Hence the
    range of `I ⟶ M` contains all commutators and so the derived subgroup.
    Therefore `I ⟶ DM` is a split epimorphism and a monomorphism, hence an
    isomorphism.
  - *Kernel.* A point killed by `q` maps into `ker π`, which is central in
    `C`. The monomorphism `D' ⟶ M' ⟶ C` reflects centrality.
- `exists_derivedSubgroup_lift`. Under the same hypotheses, with
  `IsSimplyConnectedDerivedCover dM πM` and `IsSimplyConnected D'`, there is
  `b : D' ⟶ CM` with `b ≫ πM ≫ dM = d' ≫ p`. The universal property of
  `πM` (published `IsSimplyConnectedCover.lift`, applied to the semisimple
  `D'` and the central isogeny `q`) gives `a : CM ⟶ D'` with `a ≫ q = πM`.
  By `isCentralIsogeny_of_comp`, `a` is a central isogeny from the
  semisimple `CM`. It is therefore an isomorphism because `D'` is simply
  connected. Then `b = a⁻¹`.
