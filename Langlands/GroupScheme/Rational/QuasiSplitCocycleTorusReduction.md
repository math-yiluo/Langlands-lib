# Torus reduction for cocycles of quasi-split semisimple groups

Authors: Worker 1076 and Worker 1534.

Lean module: `Langlands.GroupScheme.Rational.QuasiSplitCocycleTorusReduction`, namespace
`Langlands.GroupScheme`.

This module reduces the proof of
`Langlands.GroupScheme.QuasiSplitCocycleTorusReductionStatement.{u}` (module
`Rational/QuasiSplitCocycleTorusReductionStatement`). That statement says: every
finite-Galois cocycle `ξ` of a quasi-split semisimple group `G` over a field `K` has an
actual torus reduction (`Nonempty ξ.TorusReduction`) after a finite-Galois refinement of its
cover.

## Declarations

- `QuasiSplitCocycleTorusReductionPrerequisitesStatement` (proposition, `Prop`). It is the
  implication from three propositions at universe `u` to
  `QuasiSplitCocycleTorusReductionStatement.{u}`:
  - `SimplyConnectedCoverExistenceStatement` (module
    `SimplyConnected/CoverExistenceStatement`): every semisimple group over a field has a
    simply connected central cover;
  - `InfiniteFieldStronglyRegularPointStatement` (module
    `Rational/InfiniteFieldStronglyRegularPointStatement`): a connected reductive group over
    an infinite field has a rational point whose all-test centralizer lies in a closed torus;
  - `QuasiSplitSimplyConnectedRegularConjugateStatement` (module
    `Rational/QuasiSplitRegularConjugateStatement`): Steinberg's rational representatives of
    strongly regular classes for inner twists of simply connected quasi-split groups.
- `quasiSplitCocycleTorusReduction_of_prerequisites :
  QuasiSplitCocycleTorusReductionPrerequisitesStatement.{u}` (theorem).

No hypothesis is placed on the field: finite, infinite, perfect and imperfect fields are all
covered.

## Proof of `quasiSplitCocycleTorusReduction_of_prerequisites`

Introduce the three hypotheses, then `K`, `G` with `hG : IsSemisimple G` and
`hqs : IsQuasiSplit G`, a finite Galois extension `L/K` and a cocycle `ξ`. Split on whether
`K` is finite.

1. **`K` finite.** `Cocycle.nonempty_torusReduction_of_finite` (module
   `Rational/FiniteFieldCocycleTorusReduction`) needs only that `G` is connected reductive,
   which is `hG.isConnectedReductive`. That module shows by Lang's theorem that the cocycle
   is a coboundary, and so it reduces to the trivial torus.
2. **`K` infinite.** `not_finite_iff_infinite` gives an `Infinite K` instance. The
   conditional assembly `quasiSplitCocycleTorusReduction_of_infinite` (module
   `Rational/QuasiSplitCocycleTorusReductionInfinite`) takes seven propositions. Three are
   the hypotheses above. The other four are supplied by their proofs in the Library:
   - `finiteGaloisTwistExistence : FiniteGaloisTwistExistenceStatement` (module
     `Rational/FiniteGaloisTwistExistence`): for an affine group `G` with an automorphic
     action of a group `A`, every finite-Galois cocycle of `A` is the discrepancy of natural
     local isomorphisms from `G` to some affine group `H`;
   - `finiteGaloisFormConnectedReductive : FiniteGaloisFormConnectedReductiveStatement`
     (module `Rational/FiniteGaloisFormReductive`): a group with natural local isomorphisms
     from a connected reductive group on a finite Galois cover is connected reductive;
   - `centralIsogenyStabilizerTorus : CentralIsogenyStabilizerTorusStatement` (module
     `CentralIsogeny/StabilizerTorus`): for a central isogeny `π : G ⟶ A` and an action `a`
     of `A` on `G` with `a(π h) g = h g h⁻¹`, if the all-test centralizer of a rational
     point `x` of `G` lies in a closed torus, then the points of `A` fixing `x` under `a`
     lie in a closed torus of `A`;
   - `centralIsogenyQuasiSplitLift : CentralIsogenyQuasiSplitLiftStatement` (module
     `CentralIsogeny/QuasiSplitLift`): if the target of a central isogeny from a connected
     reductive group is quasi-split, so is its source.

   Applying the assembly to `K`, `G`, `hG`, `hqs`, `L` and `ξ` gives the reduction.

The theorem uses only `propext`, `Classical.choice` and `Quot.sound`.

## Sources and provenance

Provenance: internal. The module formalizes no separate literature statement. It combines
the two cases of the target, each documented with its sources in its own module. The case
split is that of the proof of Theorem 1.8 in R. Steinberg, *Regular elements of semi-simple
algebraic groups* (1965), source `steinberg-1965-regular-elements-semisimple-groups`,
SHA-256 `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`, §10 (printed
p.78, PDF p.31): "Assume first that k is finite. [...] By Lang's theorem [...]" and then
"Assume now that k is infinite." Passing to the simply connected covering group for a group
that is not simply connected is §11 (printed p.79, PDF p.32).

## What is not proved

The three hypotheses of `QuasiSplitCocycleTorusReductionPrerequisitesStatement` are not
proved here. Once proofs of them are in the Library, the target
`QuasiSplitCocycleTorusReductionStatement.{u}` follows by applying
`quasiSplitCocycleTorusReduction_of_prerequisites` to them.
