# Distinct Mackey components at the auxiliary place, reduced to spectral transport

This module reduces the two targets
`Proposition48ExactStabilizerDistinctnessStatement` and its totally complex form
`Proposition48ExactStabilizerDistinctnessTCStatement` to one further input,
`CuspidalArithmeticSpectralTransportStatement`. That statement says attached spectral
systems transport along isomorphisms of number fields. The module defines the two reduction
statements and proves them.

## Notation

`Q` is a Proposition 4.8 problem (Harris 1998, *The local Langlands conjecture for GL(n)
over a p-adic field, n < p*, Invent. Math. 134). `E` is a CM field, `E'/E` a finite
extension with normal closure `L`, `ξ` a Hecke character of `E'`, and `Ps.v`, `Ps.v'` the
auxiliary places of `E` and `E'`. The fields `E`, `E'`, `L` lie in `Type`. For
`a ∈ Gal(L/E)` and an intermediate field `D` of `L/E`, the Mackey field is
`C = D · a(E')` (`mackeyField`). The Mackey character is `μ_a = a(ξ) ∘ N_{C/a(E')}`
(`mackeyCharacter`), with `a(ξ) = ξ ∘ a⁻¹` the conjugate character of `a(E')`
(`conjugateCharacter`). `globalUnitComponent χ v z` is the value of the local component
`χ_v` on a global unit `z`, viewed in the completion at `v`. `Φ(z)` stands for
`globalUnitComponent ξ Ps.v' (N_{L/E'} z)` for `z ∈ Lˣ`.

## Unit components

- `unitComponent_comap`: for `e : K ≃+* L`, `(ξ ∘ e)_v(z) = ξ_{w}(e z)` with
  `w = finitePlaceEquiv e.symm v`, the place of `L` corresponding to `v`
  (`HeckeCharacter.comap_finiteComponent`).
- `unitComponent_normComp`: if `u` is the only place of `L` above `v`, then
  `(χ ∘ N_{L/K})_u(z) = χ_v(N_{L/K} z)` for `z ∈ Lˣ`. This uses the published
  `normComp_finiteComponent` and `localUnitNorm_globalUnits`. The local norm of a global unit
  is its global norm when `u` is the only place above `v`.
- `normUnits_normUnits`: `N_{M/K} ∘ N_{L/M} = N_{L/K}` on units (`Algebra.norm_norm`).
- `mackeyCharacter_unitComponent`: assume `L` has only one place above `Ps.v`. At a place
  `vC` of `C` above `Ps.v`, `(μ_a)_{vC}(N_{L/C} z) = Φ(a⁻¹ z)`. The place of `a(E')` below
  `vC` is the only place of `a(E')` above `Ps.v`, so it corresponds to `Ps.v'`. Then
  apply the previous items to `N_{C/a(E')}`, the transitivity of norms, and the
  isomorphism `E' ≃ a(E')`.
- `conjugateNormFamily_unitComponent`: let `ρ i ∈ Gal(L/D)` and let `u` be a place of `L`
  above `Ps.v`. The `i`-th conjugate `μ_a ∘ N_{L/C} ∘ ρ i` (module
  `InductionBaseChangeHeckeFamily`) has `u`-component `z ↦ Φ(a⁻¹ ρ_i z)` on global units.
  Here `ρ i` fixes `u`, since `u` is the only place above `Ps.v`.
- `isUnitary_conjugateNormFamily`: these conjugates are unitary when `ξ` is
  (`HeckeCharacter.isUnitary_comap_iff`).

## Part C: the exact-stabilizer condition separates double cosets

`not_sameFiniteComponentsAt`. Assume `L` has one place above `Ps.v` and the hypothesis
`hParent`: every `τ ∈ Gal(L/E)` with `Φ ∘ τ = Φ` on `Lˣ` fixes `E'`. Let `a`, `a'` lie in
different double cosets `Gal(L/D) a Gal(L/E') ≠ Gal(L/D) a' Gal(L/E')`, where
`Gal(L/E')` is the fixing subgroup of `conjugateField 1`. Let `ρ`, `ρ'` be families in
`Gal(L/D)` indexed by `Fin (n + 1)` and `u` a place of `L` above `Ps.v`. Then the two
conjugate families of `μ_a` and `μ_{a'}` do not have the same components at `u`
(`HeckeFamily.SameFiniteComponentsAt`: equal up to a bijection of indices).

Proof. Suppose a bijection `e` matches the components. At index `0`, the previous section
gives `Φ(a⁻¹ σ z) = Φ(a'⁻¹ σ' z)` for all `z ∈ Lˣ`, with `σ = ρ 0` and `σ' = ρ' (e 0)` viewed
in `Gal(L/E)`. Put `γ = a⁻¹ σ σ'⁻¹ a'`. Substituting `z = σ'⁻¹ a' y` gives `Φ(γ y) = Φ(y)`,
so `γ` fixes `E'` by `hParent`. Then `a' = (σ' σ⁻¹) a γ` with `σ' σ⁻¹ ∈ Gal(L/D)` and
`γ ∈ Gal(L/E')`, so `a` and `a'` lie in the same double coset (`DoubleCoset.eq`), a
contradiction.

## B6 for one tower

- `TowerBaseChangeHeckeComponentAt F K T`: the body of the published B6 statement
  `TowerBaseChangeHeckeComponentStatement.{0, 0, uV, uV}` for one prime cyclic tower `T` from
  `F` to `K` (fields in `Type`). Two unitary chains along `T` are successive weak base
  changes. They start at cuspidal realizations `S`, `S'` over `F` with unitary central
  characters and end at unitary Hecke families `μ`, `μ'` over `K`. Suppose `w` is the only
  place of `K` above a finite place `v` of `F`, and `μ` and `μ'` do not have the same
  components at `w`. Then the components at `v` of any spectral presentations of `S` and
  `S'` are not isomorphic.
- `towerBaseChangeHeckeComponentAt` and `towerBaseChangeHeckeComponentAt_of_isTotallyComplex`:
  B6, respectively its totally complex form over a totally complex `F`, gives this for every
  tower.

## Chains and the reduction with abstract inputs

- `exists_mackeyChain`: let `L/D` be Galois with a prime cyclic tower `Tw` and unitary weak
  base changes along its steps (`hBC`). Let `T` be a cuspidal realization over `D` of rank
  `r + 1` with unitary central character and class a Mackey constituent for `a`
  (`IsMackeyConstituent`: a weak automorphic induction of `μ_a`). Assume also the transport
  statement `hP` and that `ξ` is unitary. Then there are a family
  `ρ : Fin (r + 1) → Gal(L/D)` and a unitary successive weak base change chain along `Tw`.
  The chain starts at `T` and ends at the unitary Hecke family of the conjugates of `μ_a`
  by `ρ`. Here `ρ` is a right coset family for `Gal(L/C)` from `exists_isRightCosetFamily`
  (module `GaloisPlaceCount`), whose length `[C : D] = r + 1` is the rank equation of weak
  induction. The chain comes from `exists_isobaricChain_endsAtHeckeFamily` (module
  `WeakInductionTowerChain`).
- `hasDistinctMackeyComponents_of_tower`: assume `hP`, unitary weak base changes along every
  step of every prime cyclic tower from `D` to `L`, and `TowerBaseChangeHeckeComponentAt`
  for every such tower. If `Q` is `IsAuxiliaryExactStabilizerValid`, then
  `Q.HasDistinctMackeyComponents D`. The proof:
  1. From validity: `L` is the normal closure of `E'/E`, so `L/E` and `L/D` are Galois.
     `L` has one place above `Ps.v`. `ξ` is conjugate inverse, hence unitary
     (`HeckeConjugateInverse.isUnitary_of_isConjugateInverse`). Harris's exact-stabilizer
     condition (4.12) gives `hParent` through the published criterion
     `exactWeilStabilizer_iff_global`.
  2. `Gal(L/E)` is solvable (`isSolvable_of_hasUniquePlaceAbove`, module
     `UniquePlaceCyclicTower`), hence so is its subgroup `Gal(L/D)`, and `L/D` has a prime
     cyclic tower `Tw` (`nonempty_of_isSolvable`). The adele quotients are compact by the
     published `compactSpace_adeleQuotient`.
  3. For Mackey constituents `T` of `a` and `U` of `a'` with `a`, `a'` in different double
     cosets, `exists_mackeyChain` gives the two chains. For a place `w` of `D` above
     `Ps.v`, pick a place `u` of `L` above `w`. It is the only one, since `L` has only one
     place above `Ps.v`. Part C shows that the two Hecke families have different components
     at `u`, and B6 for `Tw` gives that the components of `T` and `U` at `w` differ.

## The reduction statements

- `Proposition48ExactStabilizerDistinctnessReductionStatement.{uF, uV}`:
  `CuspidalArithmeticSpectralTransportStatement.{0, 0, uV}` implies
  `Proposition48ExactStabilizerDistinctnessStatement.{uF, uV}`.
- `Proposition48ExactStabilizerDistinctnessTCReductionStatement.{uF, uV}`: the same
  implication with the totally complex target
  `Proposition48ExactStabilizerDistinctnessTCStatement.{uF, uV}`.
- `proposition48ExactStabilizerDistinctnessReduction`: proof of the general reduction.
  The B6 premise gives `TowerBaseChangeHeckeComponentAt` for every tower. The
  III.4.2(c) premise gives the steps (`exists_weakBaseChange_step`). Then apply
  `hasDistinctMackeyComponents_of_tower`.
- `proposition48ExactStabilizerDistinctnessTCReduction`: the same with the totally complex
  premises. `D` is totally complex because the CM field `E` is
  (`isTotallyComplex_of_algebra`), so the totally complex forms of B6 and III.4.2(c) apply
  (`exists_weakBaseChange_step_of_isTotallyComplex`).

The proofs do not use the rigidity premise, the prime cyclic step hypothesis
`IsPrimeCyclicStep D`, the Mackey-class count `Nat.card (MackeyIndex D) = [D : E]`, or the
uniqueness part of III.4.2(c).

## Provenance

Harris 1998, proof of Proposition 4.8 (printed pp. 202–203) and condition (4.12) in the
proof of Lemma 4.7 (printed p. 204): the Mackey constituents of different double cosets are
separated at the auxiliary place. This module derives the separation from the tower
comparison B6 (`TowerBaseChangeHeckeComponentStatement`) and Arthur–Clozel, *Simple
Algebras, Base Change, and the Advanced Theory of the Trace Formula*, III.4.2(c), along the
route of the target module's Markdown. The tower comes from the solvability of `Gal(L/E)`,
not from the prime cyclic step hypothesis. The transport statement
`CuspidalArithmeticSpectralTransportStatement` is an extra hypothesis. The chain must start
over a level field of the tower and end over `L`, and those are identified with `D` and `L`
only by isomorphisms.
