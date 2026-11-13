# A Galois-twisted special-linear presentation of simply connected type A

Author: Worker 195.

Module: `Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleStatement`.

`Langlands.GroupScheme.SpecialLinearTitsCocycleStatement.{u}` is a
prerequisite statement for the outer type A part of the local rank-one
classification. It is not proved here. It splits a simply connected
group of absolute type `A_n` over a finite Galois extension `L/K` by an
explicit local isomorphism with `SL_(n+1)`, records the Galois discrepancies
of that isomorphism as explicit matrix automorphisms, and places the actual
maximal split torus in the diagonal torus with explicit weights. Descent
of this datum to Hermitian or central simple models is a separate step.

## Auxiliary definitions (namespace `SpecialLinearTitsCocycle`)

For fields `K`, `L : Type u` with `Algebra K L`:

- `cover K L : Over (Spec K)` is `Spec L` with the structure map
  `algebraBaseMap K L`, that is `Spec` of `algebraMap K L`.
- `coverAut K L σ : cover K L ⟶ cover K L`, for `σ : L ≃ₐ[K] L`, is
  `Spec σ` (`galoisBaseMap K L σ`) as a morphism over `Spec K`, using the
  published `galoisBaseMap_over`. By the published `galoisBaseMap_mul`,
  `coverAut (σ * σ') = coverAut σ ≫ coverAut σ'`.
- `coefficients a : L →+* Γ(Z, ⊤)`, for a point `a : Z ⟶ cover K L` over
  `Spec K`, is the inverse of `Scheme.ΓSpecIso L` followed by the map on
  global sections of `a.left`. It is the `L`-algebra structure on global
  functions of `Z` given by `a`. The coefficient map of `a ≫ coverAut σ`
  is `coefficients a` composed with `σ`.
- `discrepancy E σ a g`, for a local isomorphism
  `E : LocalGroupIso (SL_(n+1) over K) G (cover K L)`, `σ`, `a` as above and
  `g ∈ SL_(n+1)(Γ(Z, ⊤))`, is
  `(E.toFun a).symm (E.toFun (a ≫ coverAut K L σ) g)`, transported to
  matrices by the published `SpecialLinear.pointsEquiv`. It is the matrix
  `h` with `E(a ≫ Spec σ) g = E(a) h`.

## The statement

The statement quantifies over a field `K : Type u`, a group scheme `G`
over `Spec K` with affine structure morphism and locally of finite type,
actual index data `d : TitsIndexData G`, a natural number `n` and a
bijection `e : d.Vertex ≃ Fin n`. It assumes `IsSimplyConnected G`,
`IsAbsolutelyAlmostSimple G`, and that every actual Cartan pairing
`d.cartan a b` equals `CartanMatrix.A n (e a) (e b)` (absolute type
`A_n`, with the actual Mathlib matrix having `n` rows; see the convention
remark in `InnerTypeANormOneStatement.md`). It concludes that there exist:

- a field `L : Type u` with `Algebra K L`, finite dimensional and Galois
  over `K`, and a `K`-embedding `ι₀ : L →ₐ[K] SeparableClosure K`;
- a local isomorphism `E` from `SpecialLinear.groupScheme (Fin (n+1)) K`
  to `G` over `cover K L`: for every `K`-scheme `Z` and point
  `a : Z ⟶ Spec L` over `K`, a group isomorphism
  `E(a) : SL_(n+1)(Z) ≃* G(Z)`, natural in `(Z, a)`;
- matrices `x σ ∈ GL_(n+1)(L)`, one for every `σ ∈ Gal(L/K)`;
- characters `χ i` of the actual maximal split torus `d.splitTorus`, for
  `i : Fin (n+1)`;

such that:

1. (Galois discrepancies.) For every `σ ∈ Gal(L/K)` and every absolute
   Galois element `τ` with `τ ∘ ι₀ = ι₀ ∘ σ`, every point `a : Z ⟶ Spec L`
   and every `g ∈ SL_(n+1)(Γ(Z, ⊤))`, writing `X` for the image of `x σ`
   under `coefficients a`:
   - if `d.star τ` fixes every vertex, then
     `discrepancy E σ a g = X g X⁻¹`;
   - if `d.star τ` moves some vertex, then
     `discrepancy E σ a g = X (g⁻¹)ᵀ X⁻¹`.
2. (Split torus.) For every point `a : Z ⟶ Spec L` and every point
   `s : Z ⟶ d.splitTorus`, the matrix of
   `E(a)⁻¹(s ≫ d.splitInclusion)` is the diagonal matrix whose `i`-th
   entry is the unit `χ i (s)` (read through `Gm.pointsEquiv`).
3. (Simple roots.) For every `i : Fin n`, the actual restriction
   `d.rootRestriction` of the simple root `e.symm i` equals
   `χ i.castSucc - χ i.succ` in `characterLattice d.splitTorus`.

The field is arbitrary: there is no characteristic, perfectness,
valuation or local-field restriction. The universe `u` is arbitrary and
common to `K` and `L`.

## Conventions and remarks

- The discrepancy clause is stated at every test point `(Z, a)`, not only
  at rational points. Since `E` is fixed, it determines each `x σ` up to a
  unit of `L`, and it implies the projective cocycle relation
  `x (σ * σ') ∈ Lˣ · x σ · θ^ε(σ(x σ'))`, where `θ(y) = (y⁻¹)ᵀ` and `ε` is
  1 exactly when the star action of a lift of `σ` is nontrivial: indeed
  `discrepancy E (σ * σ') a = discrepancy E σ a ∘ discrepancy E σ' (a ≫ Spec σ)`
  because `coverAut (σ * σ') = coverAut σ ≫ coverAut σ'`, the coefficient
  map of `a ≫ Spec σ` is `coefficients a ∘ σ`, and a matrix whose
  conjugation fixes every point of `SL_(n+1)` over `L`-algebras is scalar.
  This relation is not asserted separately; any consumer must derive it
  from clause 1.
- The two cases of clause 1 are stated as two implications, not as one
  equivalence with inverse transpose. For `n = 1` the star action is always
  trivial and inverse transpose is itself inner, so only the first case
  applies. For `n ≥ 2`, inverse transpose is an outer automorphism and the
  two cases are exclusive.
- Clause 1 constrains every lift `τ` of `σ`. In the intended proof, `L`
  contains a splitting field of the maximal torus of `d.pinning`, so the
  star action of `τ` depends only on `σ`.
- Clause 2 places the actual maximal split torus inside the diagonal torus
  for every point of `Spec L`. Together with clause 1, it shows that each
  discrepancy fixes the image of the split torus pointwise.
- Clause 3 relates the characters `χ` to the actual restrictions of the
  simple roots numbered by `e`: the restriction of the root numbered `i` to
  the maximal split torus is `χ_i - χ_(i+1)`. No compatibility of `E` with
  the maximal torus of `d.pinning` is asserted. For anisotropic `G` the split
  torus is trivial and all its characters are zero, so clauses 2 and 3 hold
  for every `E`; conjugating `E` by a matrix then keeps all three clauses
  while moving the diagonal torus. The provenance paragraph below describes
  a stronger choice that an intended proof can make.
- No uniqueness of `L`, `E`, `x` or `χ` is asserted.

## Provenance (derived statement)

This is a derived, project-internal formulation combining standard facts.
The registered source for the index notions is J. Tits, *Classification
of algebraic semisimple groups*, Proc. Sympos. Pure Math. 9 (1966),
33–62 (`tits-1966-classification-algebraic-semisimple`), Section 2.3
(printed p.39), where the index consists of the actual simple roots, the
zero-restriction set and the star action. The type `A_n` rows of Table II
(printed pp.54–55) describe outer forms `²A_n` through Hermitian forms,
and this statement supplies the Galois-cohomological input for that
description. The facts used in the intended proof are:

- a split simply connected group of type `A_n` over a field is `SL_(n+1)`,
  and a semisimple group of finite type splits over a finite separable
  extension;
- for `n ≥ 2`, the automorphisms of `SL_(n+1)` over a field `L` are the
  maps `g ↦ X g X⁻¹` and `g ↦ X (g⁻¹)ᵀ X⁻¹` with `X ∈ GL_(n+1)(L)`, because
  `PGL_(n+1)(L) = GL_(n+1)(L)/Lˣ` (Hilbert 90 for `𝔾_m`) and the outer
  automorphism group is that of the Dynkin diagram. For `n = 1`, all
  automorphisms are inner. The outer class of the Galois discrepancy is
  the star action, as in the Library's `starAction`: the Galois action on
  the characters of the `K`-torus of `d.pinning`, corrected by the Weyl
  group;
- the isomorphism can be chosen to carry the diagonal torus to the
  maximal torus of `d.pinning` and the standard base to the actual base
  with numbering `e`. A Weyl element moves bases, and composition with
  inverse transpose and the longest Weyl element reverses the numbering.
  Since the split torus `S` is split over `K`, every character of `S_L`
  comes from a character of `S`.
