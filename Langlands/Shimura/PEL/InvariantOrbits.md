# Invariant right orbits for commuting actions

This module is an intermediate algebraic construction for PEL level structures.
It takes a group `G`, a group `Gamma`, and a type `X` with commuting left
`Gamma` and right `G` actions. A right action is expressed by Mathlib's
`MulAction Gᵐᵒᵖ X`; `right x g` is `op g • x`. It satisfies
`right (right x g) h = right x (g * h)`. There is no topology or continuity
assumption on these actions.

For a subgroup `U`, `rightOrbitSetoid U` relates `x` and `y` exactly when
`y = right x u` for some `u` in `U`. Reflexivity, symmetry and transitivity
are proved using the unit, inverse and multiplication in `U`. `RightOrbit`
is the actual quotient by this equivalence relation. Its equality criterion
is `RightOrbit.mk_eq_mk`.

Commutation of the two actions induces the left `Gamma` action on this
quotient. Its action laws are proved by quotient induction.
`InvariantOrbit Gamma U` is the subtype of quotient classes fixed by every
`Gamma` element. The theorem `RightOrbit.mk_mem_fixedPoints` gives the exact
representative criterion: for every `gamma` there is some `u` in `U` such
that `gamma • x = right x u`. It does not demand a fixed representative.

`RightOrbit.translate g hg` sends `[x]` at level `U` to `[right x g]` at level
`V`, with hypothesis `g⁻¹ U g ≤ V` written elementwise. Well-definedness
uses the element `g⁻¹ u g` of `V`. The map is equivariant for `Gamma`, so it
restricts to `InvariantOrbit.translate`. The identity and composition laws
are proved on representatives and then on the subtype. Applying `g` followed
by `h` equals applying `g * h`, as required for right translation.
`InvariantOrbit.forget` uses the identity element and an inclusion `U ≤ V`.
`InvariantOrbit.tower` packages these maps into a functor from the existing
`CompactOpenLevel` transporter category to sets. Compactness and openness are
used only to specify that category's objects; the orbit constructions work for
all subgroups, and the functor makes no geometric or continuity claims.

The motivating original sources are Harris–Taylor, *The Geometry and
Cohomology of Some Simple Shimura Varieties* (2001), Section III.1, printed
p.91 (PDF p.99), and Kottwitz, *Points on some Shimura varieties over finite
fields*, JAMS 5 (1992), Section 5, printed pp.390–391 (PDF pp.18–19).
Harris–Taylor defines level structures by invariant `U`-orbits and gives the
right map `eta ↦ eta ∘ g` under `g⁻¹ U' g ≤ U`. Kottwitz explains the commuting
left monodromy and right similitude actions and their invariant orbit set.
These passages were read. The generic opposite-group construction and its
intrinsic proofs are derived here by Worker 142; the sources do not state this
Lean abstraction verbatim.

This is not yet the geometric PEL specialization. `X` has not been constructed
as isomorphisms of actual Tate modules, `G` has not been identified with the
PEL similitude group, and `Gamma` has not been identified with the geometric
fundamental group. The module supplies no Weil pairing, Tate twist
trivialization, base-point independence, or representability theorem. Those
remain obligations of the parent task. The same generic construction can later
serve full and prime-to-p coefficient systems without changing its definition.

The registered source identifiers and SHA-256 fingerprints are:

- `harris-taylor-2001-geometry-cohomology-simple-shimura`: `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
- `kottwitz-1992-points-shimura-finite-fields`: `c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.

The only project import is `Langlands.Shimura.Levels`; its existing transporter
category is reused directly. All new construction and proof code is by Worker
142. The module was checked in Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
