# Renard II.3.3: proof that an orbit quotient need not be Hausdorff

This module proves the unchanged published proposition
`Langlands.Topology.RenardOrbitQuotient.NonHausdorffOrbitQuotientStatement`
(statement pair `Langlands/Topology/RenardOrbitNonHausdorffStatement.lean` and
`.md`) by the theorem
`Langlands.Topology.RenardOrbitQuotient.nonHausdorffOrbitQuotient`. The target
has no universe parameters; the proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, II.3.3, printed p.44 / PDF p.50. It is the
paragraph immediately before the Lemma, which says that `G\X`, with the
quotient topology, "n'est pas nécessairement séparé". Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The
source gives no example. The construction below is a standard one, and the
statement Markdown and the task context suggest it as a possible route.

## Witnesses

- `G = Multiplicative ℤ`, the integers written multiplicatively, with Mathlib's
  group structure and its topology transported from `ℤ`. That topology is
  discrete.
- `X = OnePoint ℤ`, the one-point (Alexandroff) compactification of the
  discrete integers, with Mathlib's `OnePoint` topology.
- The action `translationAction`. An element `g` acts by
  `OnePoint.map (fun m => toAdd g + m)`, so it translates the integers by
  `toAdd g` and fixes `∞`. The lemmas `smul_coe` and `smul_infty` record these
  two cases. Both hold by `rfl`. `one_smul` and `mul_smul` are checked separately
  for `∞` and for an integer point, using `toAdd_one` and `toAdd_mul`.
  `translationAction` is a `def` marked `@[instance_reducible]` and made a local
  instance. The existential is filled with this same structure.

## The five conjuncts

1. `IsTopologicalGroup (Multiplicative ℤ)` is found by instance search.
2. `translation_continuousSMul`: the group is discrete, so by
   `continuous_prod_of_discrete_left` joint continuity of `(g, x) ↦ g • x`
   reduces to continuity of each map `x ↦ g • x`. That map is definitionally
   the underlying function of
   `Homeomorph.onePointCongr (Homeomorph.addLeft (toAdd g))`, which is the
   one-point extension of the translation homeomorphism of `ℤ`. So it is
   continuous.
3. `isLocallyProfinite_group`: `Multiplicative ℤ` is discrete, so it is
   Hausdorff and totally disconnected. It is also locally compact, because
   `ℤ` is a proper space (`Mathlib.Topology.Instances.Int`). The Library
   theorem `Langlands.Topology.isLocallyProfinite_of_mathlib` then gives the
   source predicate `IsLocallyProfinite`.
4. `isLocallyProfinite_space`: `OnePoint ℤ` is compact, so it is weakly locally
   compact. It is normal and T₁, hence Hausdorff, by Mathlib's `OnePoint`
   instances for a weakly locally compact R₁ space. It is totally separated,
   hence totally disconnected, by Mathlib's instance for the one-point
   compactification of a discrete space. The Library theorem
   `Langlands.Topology.isLocallyProfinite_of_weaklyLocallyCompactSpace`
   concludes.
5. `not_t2Space_orbitQuotient`: the quotient
   `Quotient (MulAction.orbitRel (Multiplicative ℤ) (OnePoint ℤ))`, with
   Mathlib's quotient topology, is not Hausdorff. Let `π` be the quotient map.
   - The classes `π ∞` and `π 0` are distinct. If they were equal,
     `Quotient.exact` would give some `g` with `g • 0 = ∞`. But `g • 0` is the
     integer point `toAdd g + 0`, and an integer point is never `∞`
     (`OnePoint.coe_ne_infty`).
   - Assuming `T2Space`, `t2_separation` gives disjoint open sets `U ∋ π ∞` and
     `V ∋ π 0`. The preimage `π ⁻¹' U` is open because `π` is continuous
     (`continuous_quot_mk`), and it is nonempty because it contains `∞`.
   - `ℤ` is not compact, so the integers are dense in `OnePoint ℤ`
     (`OnePoint.denseRange_coe`). Hence `π ⁻¹' U` contains an integer point
     `m`.
   - Translation by `ofAdd m` sends `0` to `m`, so `π m = π 0 ∈ V`
     (`Quotient.sound`). Then `π m` lies in both `U` and `V`, which
     contradicts disjointness.

The theorem `nonHausdorffOrbitQuotient` puts these components together as the
anonymous-constructor term
`⟨Multiplicative ℤ, OnePoint ℤ, _, _, _, translationAction, …⟩`. The group,
topology and action witnesses are exactly the instances used by the five
component proofs.

## Imports

The module imports the statement module unchanged, together with
`Mathlib.Topology.Compactification.OnePoint.Basic` and
`Mathlib.Topology.Instances.Int`. The latter supplies `ProperSpace ℤ` and
hence local compactness of the discrete integers.
