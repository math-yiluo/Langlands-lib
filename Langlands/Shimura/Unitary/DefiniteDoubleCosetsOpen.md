# Finiteness of definite double cosets for open levels

Author: Worker 19.

Let `σ` be an involution of a finite-dimensional `ℚ`-algebra `A` whose real
scalar extension is positive, and `GJ` its similitude group. This module
proves that the double coset space `GJ(ℚ) \ GJ(𝔸_f) / K` is finite for every
open subgroup `K` of `GJ(𝔸_f)` (`finite_doubleCosets_of_isOpen`). As a
corollary, the same holds for Harris's definite group
(`SecondKindInvolution.finite_doubleCosets_of_isOpen`).

The finiteness is stated as `Finite (EquivariantForms.DoubleCosets
σ.finiteAdelicDiagonal K)`. That is exactly the instance hypothesis of the
published `DefiniteFormsTowerLimit`, so for open `K` it is now provided.
The predicate `FiniteOpenDoubleCosets σ` collects it for all open `K`.

## Source

Harris (1999), Section 1, printed p. 301: the unitary group is definite,
`J_∞ = ∏ U(n)`. Section 3, printed pp. 306–308: definite forms of level `K`
are functions on the finite set `GJ(ℚ) \ GJ(𝔸_f) / K` ((3.9)). Harris's
levels `K` are compact open subgroups of `GJ(𝔸_f)`. This module proves the
finiteness for every open `K`.

The proof is derived and written for this module. It is not taken from
Harris. The finiteness for lattice levels is proved in the module
`DefiniteDoubleCosets` (candidate 312bef8a, not yet integrated). This module
adds compactness and openness of those levels and the standard finite-index
argument.

## Setting

- `σ.FiniteAdelicPoints` (published, `Adelic`) carries the subspace topology
  of `(𝔸_f ⊗ A)^× × 𝔸_f^×`. Here `𝔸_f ⊗ A` has the module topology over
  `𝔸_f` and units have the topology induced by `u ↦ (u, u⁻¹)`.
- `latticeLevel σ b`, `pointMatrix`, `pointMultiplier` and
  `finite_doubleCosets_latticeLevel` are from `DefiniteDoubleCosets`. The
  lattice level consists of the points `(x, c)` such that the matrices of
  left multiplication by `x` and `x⁻¹` in the basis `1 ⊗ b_i` are integral and
  `c, c⁻¹ ∈ Ẑ`.
- `Langlands.Global.isCompact_integralFiniteAdeles` and
  `isOpen_integralFiniteAdeles` (published): `Ẑ` is compact and open in
  `𝔸_f`.

## Declarations

- `finite_doubleCosets_of_finite_quotient`: let `ι : Γ →* G` and let
  `K₀, K` be subgroups of `G`. If `ι Γ \ G / K₀` is finite and
  `K₀ / (K ∩ K₀)` is finite, then `ι Γ \ G / K` is finite. The map
  `(q, c) ↦ [q.out · c.out]` from the product of the two finite sets is
  surjective. Given `g`, write the representative of its `K₀`-class as
  `h g k` with `h ∈ ι Γ` and `k ∈ K₀`. The representative of the coset of `k⁻¹`
  is `k⁻¹ k₁` with `k₁ ∈ K ∩ K₀`. Then `(h g k)(k⁻¹ k₁) = h g k₁`, which lies
  in the class of `g` in `ι Γ \ G / K`.
- `isCompact_scaled_integralFiniteAdeles`: for a nonzero integer `D`, the set
  `{t ∈ 𝔸_f | D t ∈ Ẑ} = D⁻¹ Ẑ` is compact. It is the image of `Ẑ` under
  multiplication by `ϕ(D)⁻¹`.
- `isCompact_latticeLevel`: the lattice level is compact.
  - The map `E : g = (x, c) ↦ ((x, x⁻¹), (c, c⁻¹))` is inducing. It is the
    subtype inclusion, followed by `u ↦ (u, op u⁻¹)` on both unit groups
    (`Units.isInducing_embedProduct`), followed by a homeomorphism removing
    `op`.
  - The image of the lattice level is the set `Z` of tuples `((y, y'), (c, c'))`
    with `y y' = y' y = 1`, `c c' = 1` and `y σ(y) = c`, the matrices of `y`
    and `y'` integral, and `c, c' ∈ Ẑ`. Every such tuple comes from a point of
    the lattice level.
  - `Z` is closed. Multiplication, `σ ⊗ 𝔸_f`, the algebra map and the matrix
    entries `y ↦ (L_y)_{ij}` are continuous for the module topology. The space
    `𝔸_f ⊗ A` is Hausdorff, since its coordinates in the basis
    `1 ⊗ b_i` are injective and continuous. Finally, `Ẑ` is closed.
  - `Z` lies in the compact set `(Box × Box) × (Ẑ × Ẑ)`. Here
    `Box = {y | D · coords(y) ∈ Ẑ^n}`, where `D` is a common denominator of the
    rational coordinates of `1`. Indeed `coords(y) = L_y coords(1)`, and
    `L_y` is integral.
  - Hence the image is compact, and so is the lattice level.
- `isOpen_latticeLevel`: the lattice level is open. It is a finite
  intersection of preimages of the open set `Ẑ` under the continuous maps
  `g ↦ (L_x)_{ij}`, `g ↦ (L_{x⁻¹})_{ij}`, `g ↦ c` and `g ↦ c⁻¹`.
- `FiniteOpenDoubleCosets σ` (definition): for every open subgroup `K` of
  `GJ(𝔸_f)`, the set `GJ(ℚ) \ GJ(𝔸_f) / K` is finite.
- `finite_doubleCosets_of_isOpen`: if `(σ.baseChange ℝ).IsPositive` and `K`
  is open, then `GJ(ℚ) \ GJ(𝔸_f) / K` is finite.
  - Take `K₀ = latticeLevel σ b` for `b = Module.finBasis ℚ A`. Its double
    coset space is finite by `finite_doubleCosets_latticeLevel`.
  - `K₀` is compact, and `K ∩ K₀` is open in `K₀`. So `K₀ / (K ∩ K₀)` is
    finite (`Subgroup.quotient_finite_of_isOpen`).
  - Conclude by `finite_doubleCosets_of_finite_quotient`.
- `finiteOpenDoubleCosets_of_isPositive`: positive involutions satisfy
  `FiniteOpenDoubleCosets`.
- `SecondKindInvolution.finite_doubleCosets_of_isOpen` and
  `SecondKindInvolution.finiteOpenDoubleCosets`: suppose `σ` is an involution
  of the second kind on an algebra finite over `E` with the definite
  signature at every real place (`HasDefiniteSignature σ n`). Then the
  rational involution `σ.rationalInvolution` satisfies the conclusions above.
  Positivity is the published `isPositive_of_hasDefiniteSignature`.

## Qualifications

- Only finiteness is proved. Neither the number of double cosets nor the
  stabilizers are computed.
- `K` is required to be open; compactness of `K` is not needed for
  finiteness.
- Depends on the not yet integrated candidates `DefiniteDoubleCosets`
  (312bef8a) and, through it, `DefiniteTraceForm` (a991e036),
  `HermiteReduction` (58a77643) and `RationalAdelicLattice` (536f38d2).
