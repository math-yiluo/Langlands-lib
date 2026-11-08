# Opposite factor pairs in Chevalley groups

This internal unit proves that the Chevalley groups of the split existence
construction have the Library's opposite factor pairs. Every nonidentity
rational point of a root subgroup has an explicit pair of points of the
opposite root subgroup whose product with it normalizes the torus. This is the
rank-one input to axiom V 5 of a valuation of the root datum (Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach*, Proposition 2.11.17 and Definition 6.1.2).
The universe and the characteristic are arbitrary.

## `SL₂` identities

For a commutative ring `R` and units `s, t`:

- `sl2Lower_mul_sl2Upper_mul_sl2Lower`:
  `[[1,0],[-s⁻¹,1]] [[1,s],[0,1]] [[1,0],[-s⁻¹,1]] = diag(s, s⁻¹) · w`, where `w` is the
  published Weyl element `sl2Weyl`.
- `sl2Upper_mul_sl2Lower_mul_sl2Upper`:
  `[[1,-t⁻¹],[0,1]] [[1,0],[t,1]] [[1,-t⁻¹],[0,1]] = diag(-t⁻¹, -t) · w`.

`innerIso_hom_eq_id_of_comm` states that inner automorphisms of a commutative
group scheme are the identity.

## Root exponentials

For Chevalley data `D` of a root datum `P` with base `b` and a commutative ring
`R` in the universe of the data:

- `corootCharRing j s` is the torus character `μ ↦ s ^ ⟨μ, α_j^∨⟩` with values in
  `Rˣ`. The published `corootChar` of `SplitExistence.Weyl` requires a field.
  Here a commutative ring is needed, because rational points are computed in
  the global sections of `Spec k`.
- `φ_sl2Upper_ring`, `φ_sl2Lower_ring` and `φ_sl2Diag_ring` express the published
  fields `φ_upper`, `φ_lower` and `φ_diag` as equalities of units.
- `x_opp_mul_x_mul_x_opp` and `x_mul_x_opp_mul_x`: for a simple root `i`, the
  products `x_{-i}(-s⁻¹) x_i(s) x_{-i}(-s⁻¹)` and `x_i(-t⁻¹) x_{-i}(t) x_i(-t⁻¹)`
  equal a torus element times `φ_i(w)`. Here `-i` denotes the index
  `P.reflectionPerm i i`. These follow from the `SL₂` identities, because `φ_i`
  is a homomorphism.
- `exists_weyl_conj_x` restates the published field `weyl_conj` with unit
  equalities.
- `reflectionPerm_neg_self` and `reflectionPerm_reflectionPerm_neg` are index
  identities: the negative of the negative is the root, and reflecting the
  negative is the negative of the reflection.
- `signUnit ε` is an integral sign `ε : ℤˣ` as a unit of the field, with
  `signUnit_mul_self`.

## Rational points of a Chevalley group

Let `G : D.ChevGroup k` over a field `k`.

- `rootPt j s` is the rational point `u_j(s)` of the root subgroup of `j`.
  `pointsEquiv_rootPt` computes its matrix as `x_j(s)`.
- `torusPt χ` is the rational torus point of a character `χ`. Its matrix is the
  diagonal `torusHom χ` (`pointsEquiv_torusPt`), and it centralizes the torus
  (`torusPt_mem_centralizerPoints`).
- `weylPoint_mem_normalizerPoints` states that the published Weyl point `n_i`
  normalizes the torus.
- `rootPt_opp_mul_rootPt_mul_rootPt_opp` and `rootPt_mul_rootPt_opp_mul_rootPt`
  are the two rank-one identities above for rational points of a simple root
  `i`. Each product equals a torus point times `n_i`, and so lies in the
  normalizer. The proofs cancel the closed embedding into `GL_n` and compare
  matrices.
- `exists_weylPoint_conj_rootPt`: conjugation by `n_i` sends `u_j(s)` to
  `u_{s_i j}(ε s)` for a sign `ε` independent of `s`.

`OppositeRootProperty α` states that for every unit `S` there is a sign `ε`
such that `u_{-α}(ε S⁻¹) u_α(S) u_{-α}(ε S⁻¹)` normalizes the torus.

- It holds for simple roots and their negatives, with `ε = -1`
  (`oppositeRootProperty_simple`, `oppositeRootProperty_neg_simple`).
- It is preserved by simple reflections (`oppositeRootProperty_reflect`). The
  proof conjugates the product by `n_j` and tracks the three signs.
- `oppositeRootProperty_all` proves it for every root and its negative, by
  Mathlib's `RootPairing.Base.induction_reflect`. It assumes the index type is
  finite and the root datum is reduced.

## Opposite factor pairs

For a finite, reduced root datum with finite free weight lattice, and `G.H`
affine and locally of finite type:

- `rootPt_mem` and `rootPt_mem_neg` place the root points in the intrinsic root
  subgroups of `charOf k (P.root j)` and of its negative.
- `exists_isOppositeFactorPair_rootPt` states that `(u_{-j}(ε S⁻¹), u_{-j}(ε S⁻¹))`
  is a published `RelativeRoot.IsOppositeFactorPair` of `u_j(S)` for some sign
  `ε`.
- `hasOppositeFactorPairs` proves the published
  `RelativeRoot.HasOppositeFactorPairs G.t`, given the instances
  `IsAffineHom G.H.X.hom` and `Mono G.t.hom.hom.left`. Every nonidentity
  rational root point is a root point with a unit coordinate, by the published
  `rootCoordEquiv`.

## Provenance and scope

The `SL₂` computations are classical (Steinberg, *Lectures on Chevalley
groups*, §3). The rest is an internal deduction from the published split
existence construction (`φ_upper`, `φ_lower`, `φ_diag`, `weyl_conj`, `weylPoint`,
`isNormalizingPoint_weylPoint`) and the root-group coordinates of
`RootSubgroupRepresentation`. The unit proves neither uniqueness of the pairs
nor valuation axioms. Uniqueness is the published
`IsOppositeFactorPair.eq`.
