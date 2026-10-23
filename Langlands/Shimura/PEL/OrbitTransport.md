# Transport of invariant right orbits

This module extends `Langlands.Shimura.PEL.InvariantOrbits` with maps between
representative spaces. It is an intermediate algebraic construction for
base-point transport of PEL level structures. Every construction uses the
existing right orbit quotient and its fixed-point subtype; no alternative
quotient or fixed-representative condition is introduced.

## Inputs and conventions

Let `G` be a group acting on the right of types `X`, `Y` and, where needed,
`Z`. The right actions are expressed as actions of `Gᵐᵒᵖ`, with
`right x g = op g • x`. Thus `(x · g) · h = x · (g * h)`.
There are also left actions of groups `Gamma`, `Delta` and `Theta` on the
respective spaces, each commuting with its right action. All groups and spaces
may have distinct universes. There are no topology, nonemptiness, transitivity,
or freeness hypotheses.

For a subgroup `U` of `G`, `RightOrbit X U` is the quotient by
`y = right x u` for some `u` in `U`. The existing
`InvariantOrbit (X := X) Gamma U` is the subset of these classes fixed by
every element of `Gamma`.

## Maps and equivalences

`RightOrbit.map U f hf` sends `[x]` to `[f x]`, given the explicit right
equivariance law `f (right x g) = right (f x) g`. The quotient relation is
preserved using the same element `u` of `U`. `map_mk` gives this formula.
`map_id`, `map_comp`, and `map_congr` prove identity, composition, and
pointwise extensionality by quotient induction. `map_translate` proves that
this map commutes with the existing right transporter map for
`g⁻¹ U g ≤ V`; both routes send `[x]` to `[f (right x g)]` after applying
right equivariance.

Suppose `alpha : Gamma ≃* Delta` and
`f (gamma • x) = alpha gamma • f x`. `RightOrbit.map_smul` descends this
law to orbit classes. `InvariantOrbit.map` restricts the quotient map to
fixed classes: for each `delta`, use `alpha.symm delta`, apply the source
fixedness equation, and use the descended equivariance law. The group
isomorphism guarantees that every target group element is covered.

`InvariantOrbit.map_id` and `map_comp` inherit the quotient laws. In the
composition law the group isomorphism is `alpha.trans beta` and the
representative map is `k ∘ f`. `map_congr` allows different group
isomorphisms if the representative maps agree pointwise: the underlying
quotient class is unchanged, and proof irrelevance identifies the fixedness
witnesses. `map_translate` and `map_forget` give compatibility with right
transporter maps and inclusions of levels, respectively.

`InvariantOrbit.equiv` additionally takes an equivalence `e : X ≃ Y` that
satisfies these two equivariance laws. Its forward map is `map`; its inverse
uses `e.symm` and `alpha.symm`. The inverse equivariance laws are proved by
applying the injective map `e`. The inverse identities are proved by quotient
induction using the two inverse identities of `e`, then by subtype
extensionality. This construction needs no choice of orbit representative.

## Disappearance of a left-action difference

The key law is `InvariantOrbit.map_eq_of_left`. Consider two maps `f` and
`k` as above, equivariant for possibly different isomorphisms `alpha` and
`beta` from `Gamma` to `Delta`. If there is a single `delta : Delta` such
that `k x = delta • f x` for every `x`, then their induced maps agree on
every invariant orbit.

The proof first establishes `RightOrbit.map_eq_smul` by quotient induction:
the quotient map induced by `k` is `delta` times the quotient map induced by
`f`. Its value is already a target fixed class, so this left action fixes it.
Subtype extensionality gives equality of invariant orbits.
`InvariantOrbit.equiv_eq_of_left` gives equality of the entire induced
equivalences when `f` and `k` are equivalences satisfying the same condition.
No representative is asserted to be fixed, and the maps on representatives
are not asserted to agree.

For the intended application, changing an étale path changes its induced Tate
transport by a target monodromy automorphism and changes its fundamental-group
identification by conjugation. The permission to use different `alpha` and
`beta` is therefore essential. The actual path-change equation is a separate
geometric input to this generic lemma, not a premise asserting the desired
quotient equality.

## Provenance and scope

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), Section III.1, printed p.91 (PDF p.99), defines a level structure as an
invariant right orbit, asserts canonical base-point independence, and gives
right level-change maps. Kottwitz, *Points on some Shimura varieties over
finite fields*, JAMS 5 (1992), Section 5, printed pp.390–391 (PDF pp.18–19),
explains the commuting right similitude and left monodromy actions and the
role of fixedness in base-point independence. These original passages were
read. This generic quotient-map formulation and its intrinsic proofs are
derived by Worker 142; neither source states this Lean abstraction verbatim.

This module does not construct geometric paths, Tate modules, twists, Weil
pairings, or PEL frames. It does not identify an arbitrary acting group with a
geometric fundamental group. It proves the algebraic mechanism to be applied
to those actual constructions. In particular, it does not by itself establish
the full or prime-to-p PEL moduli functor or its canonical base-point
independence. No continuity or geometric base-change assertion is made here.

Registered original sources and SHA-256 fingerprints:

- `harris-taylor-2001-geometry-cohomology-simple-shimura`:
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
- `kottwitz-1992-points-shimura-finite-fields`:
  `c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.

All new code and prose are by Worker 142. The imported invariant-orbit module
is reused unchanged. Development compilation uses Lean 4.34.0 and Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`.
