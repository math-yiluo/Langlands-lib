# Automorphisms of `SO_{2n}` fixing the diagonal torus

This module proves the root-scaling step of the computation
`Aut(SO_{2n}) = PGO_{2n}` (Knus–Merkurjev–Rost–Tignol, *The Book of
Involutions*, §26.B): an automorphism of the split `SO_{2n}`, `n ≥ 2`, that
is the identity on the diagonal maximal torus is conjugation by a diagonal
similitude. The argument is the standard one: such an automorphism scales
the simple root spaces; a diagonal similitude undoes these scalars, and an
automorphism fixing a pinning is trivial. The Lean proof follows the Library
proof of `SplitPinning.exists_eq_rootScalingIso`
(`Reductive/PinnedWeylInner`), but builds the scaling element as an explicit
diagonal matrix. The Lean formulation is internal to this project.

Notation as in `Conjugation`: `Q = formMatrix`, `IsSimilitude g c` means
`g Q gᵀ - c Q` is alternating. `w(x)` (`weightCoord`) is the weight of the
diagonal torus on the `x`-th coordinate: `w(inl a) = e_a`,
`w(inr a) = -e_a`.

## Diagonal similitudes (any commutative ring `A`)

- `diagonalUnits d`: the invertible diagonal matrix with diagonal
  `d : l ⊕ l → Aˣ`. `coe_diagonalUnits`, `coe_diagonalUnits_inv` give the
  matrix and its inverse.
- `isSimilitude_diagonalUnits d c hd`: if `d(inl a) d(inr a) = c` for every
  `a`, then `diagonalUnits d` is a similitude with multiplier `c`. In fact
  `D Q Dᵀ - c Q = 0`, checked entrywise on the four blocks of `Q`.
- `lieMatrix_smul`: `lieMatrix (c • X) = c • lieMatrix X` (linearity,
  restated with the ring `A` explicit for later use).

## Over a field `k`

Local instances restate the commutative group and `k`-module structures of
the Lie kernels of `SO_{2l}` and `O_{2l}` at coefficients
`CommRingCat.of k`. Without them instance search times out on these types.

- `identityTorus_comp_specialConjIso`: conjugation by `diagonalUnits d` is
  the identity on the diagonal torus `identityTorus l k`. On points both
  sides are diagonal matrices and diagonal matrices commute.
- `targetMapLinear_specialConjIso_diagonalUnits`: let `X` be in the weight
  space of a character `χ` of the diagonal torus, and suppose
  `d(x) / d(y) = e` whenever `χ = w(x) - w(y)`. Then the differential of
  conjugation by `diagonalUnits d` sends `X` to `e • X`. Proof: in Lie
  matrices the differential is `X ↦ D X D⁻¹`, whose `(x, y)` entry is
  `d(x) X_{xy} d(y)⁻¹`. A nonzero entry `X_{xy}` forces
  `χ = w(x) - w(y)` (`mem_weightSpace_diagonalTorus_iff_support`), so every
  entry is multiplied by `e`.

## Main theorem

`isSimilitudeConj_of_comp_identityTorus hn β hβ`: let `n ≥ 2` and `β` an
automorphism of `SO_{2n} = identityComponent (groupScheme (Fin n) k)` with
`identityTorus ≫ β = identityTorus`. Then `IsSimilitudeConj β`.

Proof.

1. `SO_{2n}` is connected reductive (`isConnectedReductive_identityComponent`)
   and the diagonal torus is a split maximal torus. `rootDatumExistence`
   gives a root datum with a base, and `SplitPinning.ofRootDatum` (with
   `splitRootLieLine`) gives a split pinning `p` whose torus inclusion is
   `identityTorus`.
2. Because `β` fixes the torus, its differential preserves each weight
   space (`lieKernelHomLinear_mem_weightSpace`). Each simple-root space is a
   line (the pinning trivialization), so `dβ(X_a) = s_a X_a` for the simple
   root vectors `X_a`, and `s_a ≠ 0` since `dβ` is injective.
3. The simple roots form a `ℤ`-basis of the root lattice
   (`Base.toWeightBasisInt`). Let `H` be the homomorphism from the root
   lattice to `kˣ` with `H(α_a) = s_a⁻¹`.
4. Every weight difference `w(x) - w(y)` is in the root lattice: if the
   indices of `x` and `y` differ it is a root (`roots_identityTorus`,
   `mem_roots_iff`). Otherwise it is a sum of two such differences through
   `inl j` for an index `j` different from that of `x` (here `n ≥ 2` is
   used).
5. Put `d(x) = H(w(x) - w(inl 0))` and `c = d(inl 0) d(inr 0)`. Then
   `d(x) / d(y) = H(w(x) - w(y))`. Also `d(inl a) d(inr a) = c` for all `a`,
   because `w(inl a) + w(inr a) = 0 = w(inl 0) + w(inr 0)`. So
   `D = diagonalUnits d` is a similitude with multiplier `c`.
6. By step 5 and `targetMapLinear_specialConjIso_diagonalUnits`, conjugation
   by `D` scales `X_a` by `H(α_a) = s_a⁻¹`. Hence `β` followed by
   conjugation by `D` fixes the torus (`identityTorus_comp_specialConjIso`)
   and every `X_a`. By `pinnedAutomorphismRigidity` it is the identity.
7. So `IsSimilitudeConj (β ≫ specialConjIso D)` holds (by
   `isSimilitudeConj_refl`), and `IsSimilitudeConj.of_trans` with
   `isSimilitudeConj_specialConjIso` gives `IsSimilitudeConj β`.
