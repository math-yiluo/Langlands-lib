# Canonical homeomorphism from stabilizer cosets to a locally closed orbit

This module constructs `Langlands.Geometric.cosetOrbitHomeomorph`. For a
locally compact, sigma-compact topological group `G`, closed subgroups `P,Q`,
and `w : G` whose orbit `cosetOrbit P Q w` is locally closed, it gives

```
Induction.LeftQuotient (orbitStabilizer P Q w) ≃ₜ cosetOrbit P Q w.
```

The universe of `G` is arbitrary. The domain has its existing quotient topology;
the codomain has the subspace topology inherited from `Induction.LeftQuotient P`.
The representative formula is

```
[ q ] ↦ [ w⁻¹ * q ],   q : Q.
```

Here the source coset is `(Q ∩ w P w⁻¹) q` within `Q`, and the target coset is
`P w⁻¹ q`. No subgroup is required to be open, and neither an open orbit map
nor a local section is an assumption. The construction applies in particular
to every locally compact Hausdorff sigma-compact group in the task. A separate
`T2Space G` hypothesis is unnecessary: the imported closed-subgroup quotient
result already gives the Hausdorff property of `P \ G` that this proof uses.

## Construction and intrinsic laws

`cosetOrbitMap` is the canonical map from `Q` to the range subtype defining
`cosetOrbit`. `cosetOrbitMap_eq_iff` proves that two representatives `q,r` have
the same image exactly when they are related by
`QuotientGroup.rightRel (orbitStabilizer P Q w)`. Expanding the left quotient
relation reduces this to the identity

```
(w⁻¹ * r) * (w⁻¹ * q)⁻¹ = w⁻¹ * (r * q⁻¹) * w.
```

Membership of the right side in `P` is precisely membership of `r * q⁻¹` in
the published stabilizer. `cosetOrbitQuotientMap` descends this map by
`Quotient.lift`. Its injectivity follows from the relation characterization;
its surjectivity follows from the range definition of `cosetOrbit`.
`cosetOrbitEquiv` packages the resulting algebraic equivalence and requires no
topological hypotheses.

`isClosed_orbitStabilizer` pulls the closed set `P` back along the continuous
map `q ↦ w⁻¹ * q * w`. `continuous_cosetOrbitMap` composes the continuous group
map with the ambient quotient projection and restricts its codomain to the
orbit. `continuous_cosetOrbitQuotientMap` then descends continuity through the
source quotient topology.

For openness, `isOpenMap_cosetOrbitMap` reuses the published inverse right
action `leftQuotientAction` and its joint continuity. The quotient by `P` is
locally compact by `QuotientIntegration.leftQuotient_locallyCompactSpace` and
Hausdorff by `QuotientIntegration.leftQuotient_t2Space`. A locally closed
subspace of that quotient is locally compact, hence a Baire space. Closedness
of `Q` in sigma-compact `G` makes `Q` sigma-compact. The restricted action on
its orbit is continuous and transitive, so Mathlib's
`isOpenMap_smul_of_sigmaCompact` proves that its orbit map is open.
`leftQuotientAction_orbit` identifies the action orbit with `cosetOrbit`, and
precomposition with inversion on `Q` changes inverse right translation into
the required map `q ↦ P w⁻¹ q`.

The bijection on stabilizer cosets is open because the image of an open set
in the quotient is the image, under `cosetOrbitMap`, of its open inverse image
in `Q`. `Equiv.toHomeomorphOfContinuousOpen` therefore supplies inverse
continuity and the actual homeomorphism.

`cosetOrbitHomeomorph_mk` is the representative formula in the ambient left
quotient. `cosetOrbitHomeomorph_symm_map` simplifies the inverse at an orbit
point presented by `q`. Both are simp lemmas. The module also exposes
`continuous_cosetOrbitHomeomorph` and
`continuous_cosetOrbitHomeomorph_symm`; all usual homeomorphism laws remain
available from the bundled result.

## Provenance and source correspondence

This is a derived construction using published Library definitions and
Mathlib's open mapping theorem, rather than an additional assumed interface.
Its motivating original is Bernstein and Zelevinsky, *Induced representations
of reductive p-adic groups I* (1977), sections 5.14–5.15, printed pages 464–465,
PDF pages 25–26. These original pages were read in full. No source-specific
erratum was found in the project's notes.

Section 5.14 identifies a transitive l-space for an l-group countable at
infinity with the quotient by a point stabilizer, referring to [I], 1.5.
Section 5.15, Case III, identifies the orbit of the identity coset with
`(P ∩ Q) \ Q`. The current formula transports this identification to the
published representative convention `P w⁻¹`, whose stabilizer is
`Q ∩ w P w⁻¹`. Countability at infinity is used through sigma-compactness.
The implementation proves the broader topological-group result directly
using Mathlib; it does not assert that BZ77 states this broader version or
formalize the sheaf equivalences discussed on those pages. No dependence on
the proof in reference [I] is needed.

The source is registered as `bernstein-zelevinsky-1977-induced-i`, with
SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The direct proof reuses
`Mathlib.Topology.Algebra.Group.OpenMapping`,
`Mathlib.Topology.Baire.LocallyCompactRegular`, and
`Mathlib.Topology.Homeomorph.Lemmas` from the project's pinned Mathlib.
Existing definitions and quotient-topology results are imported through
`Langlands.Representation.Geometric.CosetAction`; no imported pair is modified.

Author: Worker 182.
