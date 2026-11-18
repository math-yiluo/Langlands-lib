# The Tits class of a dominant star-fixed weight

This module attaches a Brauer class to every dominant weight fixed by the
star action. Fix Galois pinning data `d : GaloisPinningData k K G` for an
affine, locally finite type group scheme `G` over a field `k`, with `K/k`
Galois (for instance `K` a separable closure of `k`). Let `λ` be a dominant
weight of the split torus `T_K` with `d.IsStarFixedWeight λ` (published,
module `Reductive/InnerStarWeights`). Let `ρ` be a representation of `G_K`
on `Kⁿ` with `d.toSplitPinning.IsHighestWeight ρ λ` (published,
`Rational/FundamentalRepresentations`). This predicate has four conjuncts:
`ρ` is irreducible, the weight spaces of `ρ` span `Kⁿ`, the `λ`-space is
one-dimensional, and `λ − μ` lies in the positive root monoid for every weight
`μ` of `ρ`. Irreducibility is essential. A representation in which `λ` is
merely a dominant weight of multiplicity one above all other weights need not
have a simple coefficient algebra. For example, take split `SL₂` over `ℚ`,
`K` an algebraic closure of `ℚ` and the base change of `Sym²(ℚ²) ⊕ ℚ`: its
coefficient algebra maps onto `ℚ` by projection to the trivial summand, with
nonzero kernel. For `ρ` satisfying `IsHighestWeight`,
the Tits algebra `titsAlgebra ρ` (module `MatrixRepresentation/TitsAlgebra`)
is a central simple `k`-algebra. Its class in Mathlib's `BrauerGroup k` is
the same for every such `ρ` with the same `λ`. This
is the matrix-coordinate counterpart of the class `[D]` that Tits,
*Représentations linéaires irréductibles d'un groupe réductif sur un corps
quelconque*, J. reine angew. Math. 247 (1971), Théorème 3.3, printed
pp. 203–204, attaches to an invariant dominant weight. In Tits's proof the
descended algebra is obtained by twisting a representation of a split form by
a projective cocycle; here it is the coefficient algebra of a representation
of `G_K` with Galois intertwiners (see `MatrixRepresentation/TitsAlgebra`).

The theorem of the highest weight is the published
`splitHighestWeightClassification` (`Rational/SplitHighestWeightClassificationProof`).
All three of its clauses are stated with the `IsHighestWeight` predicate, so
they concern irreducible representations. It supplies, for each dominant `λ`,
a representation `ρ` on some `Kⁿ` with `IsHighestWeight ρ λ`. Two
representations `ρ`, `ρ'` with `IsHighestWeight ρ λ` and
`IsHighestWeight ρ' λ'` admit a bijective intertwiner exactly when `λ = λ'`.
Every irreducible representation satisfies `IsHighestWeight` for a unique
dominant weight. The public signatures below therefore take no classification
hypothesis.

## Declarations

- `coefficientMatrix_intertwines_of`: an intertwiner `C` from `ρ` to `τ` (a
  rectangular matrix) satisfies `C · X_φ(ρ) = X_φ(τ) · C` for every coefficient
  matrix. It is obtained by applying `id ⊗ φ` to the universal intertwining
  identity (`intertwines_iff_universalMatrix`).
- `conjAlgEquiv C D hCD hDC` is conjugation `X ↦ C X D` by mutually inverse
  rectangular matrices, as a `k`-algebra equivalence `M_n(K) ≃ M_m(K)`.
- `titsAlgebra_map_conjAlgEquiv` and `titsAlgebraEquivOfIntertwines`: conjugation
  by a bijective intertwiner carries `titsAlgebra ρ` onto `titsAlgebra τ`, since
  the generators correspond (`AlgHom.map_adjoin`). So isomorphic representations
  have isomorphic Tits algebras.
- `smul_eq_weightEquiv` identifies the action of root datum automorphisms with
  their weight map. `isUnit_of_bijective_mulVecLin`: a matrix whose linear map
  is bijective is a unit.
- `exists_intertwiner_galoisTwist`: let `IsHighestWeight ρ λ` hold with `λ`
  star fixed. For every `σ` there is an invertible intertwiner `ρ → ρ^σ`.
  Indeed `IsHighestWeight ρ^σ λ` holds by `isHighestWeight_galoisTwist`
  (`Reductive/GaloisTwistWeights`), and the uniqueness clause of
  `splitHighestWeightClassification` gives a bijective intertwiner.
- `nonempty_of_isHighestWeight`: if `IsHighestWeight ρ λ` holds, then `ρ` acts
  on a nonzero space, because its `λ`-space has dimension one.
- `titsCSAOf hρ hfix`, for `hρ : IsHighestWeight ρ λ` and `λ` star fixed, is
  the Tits algebra of `ρ` as an element of Mathlib's `CSA k` (`titsCSA`).
  Irreducibility is the first conjunct `hρ.1`. The required intertwiners `P σ`
  are chosen from
  `exists_intertwiner_galoisTwist`. Scalar self-intertwiners come from the
  published `IsHighestWeight.intertwiner_eq_scalar`.
- `dominantTitsClass λ hdom hfix : BrauerGroup k` is the class of
  `titsCSAOf` for the representation `ρ` with `IsHighestWeight ρ λ` that
  `splitHighestWeightClassification` provides for the dominant weight `λ`.
- `titsCSAOf_isBrauerEquivalent` and `dominantTitsClass_eq`: let `ρ` and `ρ'`
  satisfy `IsHighestWeight ρ λ` and `IsHighestWeight ρ' λ`, possibly on spaces
  of different dimensions. Then their Tits algebras are Brauer equivalent.
  They are isomorphic by the uniqueness clause of
  `splitHighestWeightClassification`, and their Tits algebras are
  isomorphic as `k`-algebras (`titsAlgebraEquivOfIntertwines`, then
  `AlgEquiv.mapMatrix` with `1 × 1` matrices). Hence `dominantTitsClass` is the
  class of the Tits algebra of every `ρ` with `IsHighestWeight ρ λ`. This is
  independence of the auxiliary choice of representation. No claim is made for
  representations that are not irreducible.

No characteristic, perfectness or reducedness assumption is made. The CSA
representatives live in `Type u`, the universe of `k`.
