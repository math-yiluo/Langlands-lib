# Conjugation by similitudes of the split quadratic form

This module sets up the automorphisms of the split orthogonal group `O_{2l}`
and of its identity component `SO_{2l}` given by conjugation by a similitude.
It also defines the predicate `IsSimilitudeConj`, which is the body of the
Library statement `SpecialOrthogonalAutomorphismStatement`. The module is
infrastructure for the proof of that statement. Its content is standard
(Knus–Merkurjev–Rost–Tignol, *The Book of Involutions*, §12 for similitudes
and §26.B for `Aut(SO_{2n})`); the Lean formulation is internal to this
project.

Notation: `Q = formMatrix l A` is the Gram matrix of the split (hyperbolic)
quadratic form `q(x) = ∑ a, x (inl a) * x (inr a)` on `A^(l ⊕ l)`. `IsAlt M`
means `M = U - Uᵀ` for some `U`.

## Similitudes (any commutative ring `A`)

- `IsSimilitude g c`: `g Q gᵀ - c Q` is alternating. For a nondegenerate
  form this says `q(g x) = c q(x)`, the standard definition of a similitude
  with multiplier `c`. Here it is the definition itself.
- `isSimilitude_one_iff`: the similitudes with multiplier `1` are exactly
  the elements of `orthogonalGroup l A`. `isSimilitude_one`: `1` is one.
- `IsSimilitude.map`: similitudes are preserved by ring homomorphisms
  (entrywise).
- `IsSimilitude.mul`: `g h` is a similitude with multiplier `c d`. Proof:
  `g h Q (g h)ᵀ - c d Q = g (h Q hᵀ - d Q) gᵀ + d (g Q gᵀ - c Q)`, and
  alternating matrices are stable under congruence, scaling and sums.
- `IsSimilitude.inv`: if `g' g = 1` and `c' c = 1` then `g'` is a
  similitude with multiplier `c'`, because
  `g' Q g'ᵀ - c' Q = -c' g' (g Q gᵀ - c Q) g'ᵀ`.
  `IsSimilitude.units_inv` is the special case of an invertible matrix and a
  unit.
- `IsSimilitude.conj_mem`: if `x` is orthogonal then so is `g x g'`, by
  `mul` and `inv` with multiplier `c · 1 · c' = 1`.

## Conjugation on `O_{2l}` over a ring `R`

- `conjHom g c hg`: `x ↦ g x g⁻¹` as a group endomorphism of
  `orthogonalGroup l A` (`coe_conjHom` is its formula).
- `IsSimilitude.mapGL`: `IsSimilitude.map` for an invertible matrix and a
  unit.
- `conjTrans R g c hg`: the natural transformation of the point functor
  `functor l R` with components `conjHom` of the images of `g` and `c` in
  each `R`-algebra.
- `conjMap R g c hg`: the induced endomorphism of the group scheme
  `groupScheme l R`, through the corepresentability of the point functor.
- `pointsEquiv_conjMap` and `affinePointsEquiv_conjMap`: on points over a
  test scheme `T` (resp. an `R`-algebra `S`) the map is `x ↦ g x g⁻¹`, with
  the entries of `g` and `g⁻¹` mapped to `Γ(T, ⊤)` (resp. `S`).
- `map_units_inv_mul`, `map_mul_units_inv`: images of `g⁻¹ g = 1` and
  `g g⁻¹ = 1` under a ring homomorphism.
- `conjMap_comp_conjMap`: conjugating by `g`, then by `h`, is conjugating by
  `h g` (with multiplier `d c`). `conjMap_one`: conjugation by `1` is the
  identity. Both are checked on points.
- `conjIso R g c hg`: the automorphism of `groupScheme l R`, with inverse
  conjugation by `g⁻¹`.
- `lieMatrix_targetMapLinear_conjMap`: the differential of `conjMap` sends
  the Lie matrix `X` to `g X g⁻¹`. Proof: a Lie algebra element is a point
  over the dual numbers `A[ε]` with matrix `1 + ε X`; conjugating gives
  `1 + ε g X g⁻¹`, and comparing `ε`-components gives the claim.

## Restriction to `SO_{2l}` over a field `k`

- `specialConjIso g c hg`: `conjIso` restricted to the identity component,
  via `IdentityComponent.mapIso`.
- `specialConjIso_hom_identityComponentι` (with a `reassoc` form): it is
  compatible with the inclusion `SO_{2l} ⟶ O_{2l}`.
- `IsSimilitudeConj α`: there are `g ∈ GL_{2l}(k)` and `c ∈ kˣ` with
  `IsSimilitude g c` such that, for every test scheme `T` and point `x` of
  `SO_{2l}`, the matrix of `α(x)` is `g x g⁻¹` (entries of `g`, `g⁻¹` mapped
  to `Γ(T, ⊤)`). Once `IsSimilitude` is unfolded, the body of
  `SpecialOrthogonalAutomorphismStatement` for `L = k`, `l = Fin n` is
  literally `IsSimilitudeConj α`.
- `isSimilitudeConj_specialConjIso`: `specialConjIso g c hg` satisfies
  `IsSimilitudeConj` with this `g`.
- `isSimilitudeConj_refl`, `IsSimilitudeConj.trans`,
  `IsSimilitudeConj.symm`: the predicate holds for the identity, and is
  closed under composition (with `g' g`, multiplier `c' c`) and inversion
  (with `g⁻¹`, `c⁻¹`). `IsSimilitudeConj.of_trans`: if `α ≫ β` and `β`
  satisfy the predicate then so does `α`, since `α = (α ≫ β) ≫ β⁻¹`.
- `lieMatrix_targetMapLinear_specialConjIso`: the differential of
  `specialConjIso`, read in Lie matrices of `O_{2l}`, is `X ↦ g X g⁻¹`.
  This follows from `lieMatrix_targetMapLinear_conjMap` and the
  compatibility with the inclusion.
