# Evaluation of actual formal line bundles on Artinian tests

This is an internal construction from the published `Deformation.ArtinianTests`
and `Picard.FormalLineBundleSystem` modules and Mathlib's ideal quotient maps.
It supplies finite-stage evaluation by ordinary pullback, a prerequisite for
relating a formal family to actual Artinian deformations. No external
representability theorem is used.

## Parameters and finite factorization

All types and schemes have arbitrary universe `u`. The base `k` is a
commutative ring, `K` is a field with a specified `k`-algebra structure, and
`R` is any commutative `k`-algebra. An actual `ArtinianTest k K` has a local
Artinian underlying algebra `A.algebra` and its specified surjective
augmentation to `K`. It need not carry a `K`-algebra structure.

Fix an ideal `I` of `R` and an actual `k`-algebra map `α : R →ₐ[k] A.algebra`.
`IsBound I α n` is the proposition that `I^(n+1)` lies in the kernel of `α`.
`IsBound.mono` proves that a bound remains valid at every later index.

`exists_bound` assumes a specified augmentation `ε : R →ₐ[k] K`, the
inclusion `I ≤ ker ε`, and the equality `A.augmentation.comp α = ε`.
It proves that a bound exists. The proof maps `I` into the kernel of the
augmentation of `A`, which is its maximal ideal. Nilpotence of this maximal
ideal then forces a power of `I` into the kernel of `α`. It does not assume
that `R` is local, Noetherian, complete, or of finite type, or that `K` is a
finite extension of `k`.

For every bound, `factor` is the actual quotient algebra map
`R / I^(n+1) →ₐ[k] A.algebra`. `factor_comp_mk` proves its factorization
identity. `factor_transition` proves that these factor maps agree under the
consecutive quotient map. The private ordinary-ring lemma
`quotient_lift_comp_factor` proves this by the universal property of the
quotient, using the quotient lift and factor composition identities.

## Actual scheme maps and evaluation

For an actual scheme morphism `f : Y ⟶ Spec R`, `testSpace α f` is the
ordinary scheme pullback `Y ×[Spec R] Spec A`. The published adic space is
`Y ×[Spec R] Spec (R/I^(n+1))` with the same pullback order.

`baseMap` is the spectrum map of `factor`. `baseMap_projection` and
`baseMap_transition` prove its compatibility with the original base and
consecutive adic base maps. The universal property of the scheme pullback
gives `spaceMap` from `testSpace α f` to the actual adic space.
`spaceMap_projection` and `spaceMap_transition` prove the corresponding
compatibilities for the total spaces.

If `F` is an actual `FormalLineBundleSystem f I`, `evaluate I α f F n h`
is the ordinary pullback of its actual stage bundle `F.obj n` along
`spaceMap`. It is a line bundle on `testSpace α f`, with no quotient of its
isomorphisms or replacement by isomorphism classes.

`stepIso` compares the evaluation at `n+1` to that at `n`. It uses the
proved equality of the actual space maps, the ordinary pullback-composition
isomorphism, and the system's original specified transition isomorphism.
`laterIso` iterates these specified comparisons for every `n ≤ m`.
`boundsIso` compares evaluation at any two valid bounds through their
maximum. Thus choosing a valid bound gives isomorphic ordinary bundles;
no equality of bundles at distinct indices is asserted.

`comparisonIso` pulls back the stage component of any compatible comparison
of formal systems to obtain an isomorphism of their evaluations at that
stage. These declarations do not assert additional coherence equations
between the constructed comparison isomorphisms.

## Comparison with an actual algebraization

For an actual line bundle `L` on `Y` and a compatible comparison
`ofLineBundle f I L → F`, `algebraizationIso` gives an actual isomorphism
from the ordinary pullback of `L` to `testSpace α f` to `evaluate F n h`.
Its implementation uses `spaceMap_projection`, the ordinary
pullback-composition isomorphism, and the original comparison component.
It works at every specified valid bound.

This construction does not supply a formal system, a versal hull, an
algebraization, formal versality, openness, or a smooth atlas. It also does
not identify this pullback order with the opposite order used by
`Picard.relativeSpace`; any later use there needs the actual comparison.
