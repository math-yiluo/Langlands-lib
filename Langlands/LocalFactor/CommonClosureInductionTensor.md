# The projection formula for tensor products and induction

Lean module: `Langlands.LocalFactor.CommonClosureInductionTensor`. It imports
`Langlands.LocalFactor.CommonClosureInductionTwist` (for `weilInclusion`),
`Langlands.VirtualRepresentation.ExactTensor` and Mathlib's
`Mathlib.LinearAlgebra.TensorProduct.Pi`.

The Library already has the projection formula for a scalar character
(`FiniteRepresentation.induceTwistEquiv`,
`ExactGrothendieckGroup.continuousInduce_continuousTwist`,
`CommonClosure.continuousTwist_induce`). This module proves it for an arbitrary
finite-dimensional tensor factor:
`A ⊗ Ind_S B ≅ Ind_S (A|_S ⊗ B)`.
It does so on the actual induced spaces, on the actual exact virtual groups of
continuous representations, and on the common-closure exact virtual groups.

## Actual representations (`Langlands.FiniteRepresentation`)

The project's induction `FiniteRepresentation.induce S B` is Mathlib's
coinduced space `Representation.coindV S.subtype B.representation`. Its
elements are the functions `f : G → B` with `f (s * g) = B s (f g)`, and `G`
acts by right translation. Here `S` is a finite-index subgroup of the group `G`
and `K` is any field.

- `actionLinearEquiv A g`: the action of `g` on `A` as a linear
  automorphism, with inverse the action of `g⁻¹`.
- `induceTensorLinearEquiv S φ A B`: a linear equivalence
  `tensor A (induce S B) ≃ₗ[K] induce S (tensor (restrict φ A) B)`, for any
  `φ : S →* G`. It is the composite of four equivalences:
  - the coset coordinates `Induction.coordinates` on the right factor
    (values on the chosen right-coset representatives);
  - Mathlib's `TensorProduct.piRight`, `A ⊗ (Cosets → B) ≅ Cosets → (A ⊗ B)`;
  - at each coset `q`, the action of its representative `q.out` on the `A`
    factor;
  - the inverse coset coordinates of the target.
- `induceTensorLinearEquiv_tmul S φ hφ A B a f g`: if `φ s = s` for every
  `s` (`hφ`), the image of `a ⊗ f` is the function
  `g ↦ A g a ⊗ f g`. The proof writes `g` as its subgroup factor times its coset
  representative (`Induction.factor_mul_out`) and uses the equivariance of
  `f`.
- `induceTensorEquiv S φ hφ A B`: the same map as an intertwining
  equivalence. `Equiv (tensor A (induce S B)) (induce S (tensor (restrict φ A) B))`
  holds for any restriction `φ` acting as the inclusion. The intertwining
  property is checked on pure tensors with `induceTensorLinearEquiv_tmul`.
  Both sides send `a ⊗ f` and `h` to `g ↦ A (g * h) a ⊗ f (g * h)`.
- `restrictTensorEquiv ψ φ A B`: the identity map is an equivalence
  `tensor (restrict (ψ.comp φ) A) (restrict φ B) ≅ restrict φ (tensor (restrict ψ A) B)`.
  It holds for monoid homomorphisms `ψ : H →* G` and `φ : J →* H`. Both sides
  have the same carrier and the same action.

## Exact virtual groups (`Langlands.VirtualRepresentation.ExactGrothendieckGroup`)

- `continuousTensor_continuousInduce S hS w x` applies to an open
  finite-index subgroup `S` of a topological group `G`, with
  `w : Continuous G` and `x : Continuous S`. It states
  `continuousTensor w (continuousInduce S hS x) =
    continuousInduce S hS (continuousTensor (continuousRestrict ⟨S.subtype, _⟩ w) x)`.
  Both sides are `ℤ`-bilinear. By `hom_ext`, first in `w` and then in `x`, it
  suffices to check genuine continuous representations. There the two classes
  are equal by `ofRepresentation_eq_of_equiv` and `induceTensorEquiv` with
  `φ = S.subtype`.

## Common-closure groups (`Langlands.LocalFactor.CommonClosure`)

- `continuousTensorSame_induce F E L h w x` applies when
  `E.field ≤ L.field`, with `w : Virtual F E` and `x : Virtual F L`. It states
  `continuousTensorSame w (induce F E L h x) =
    induce F E L h (continuousTensorSame (continuousRestrict (weilInclusion F E L h) w) x)`.
  `CommonClosure.induce` is `ExactGrothendieckGroup.induce` from the
  rebracketed subgroup `(weilSubgroup F L).subgroupOf (weilSubgroup F E)`,
  after restriction along `nestedWeilEquiv`. On genuine classes, the required
  equivalence is `induceTensorEquiv` for `φ` the inclusion composed with
  `nestedWeilEquiv`, which acts as the inclusion definitionally. It is followed
  by the induction of `restrictTensorEquiv`. Bilinearity and `hom_ext` give the
  general case, as for the exact virtual groups.

## Sources

- Serre, *Linear Representations of Finite Groups* (1977), §7.2, Remark (3),
  printed p. 57 (PDF p. 65): `Ind(W) ⊗ E ≅ Ind(W ⊗ Res E)`, citing §3.3,
  Example 5. Serre states it for finite groups. The proof here is the
  explicit isomorphism `a ⊗ f ↦ (g ↦ A g a ⊗ f g)` on the equivariant-function
  model. It needs only that `S` has finite index and that the representations
  are finite-dimensional.
- Deligne–Henniart (1981), §4.5 (printed p. 110, PDF p. 22) uses this formula
  implicitly. The step `ε(W ⊗ V, ψ) = ∏ ε(W_i ⊗ V_i, ψ ∘ Tr_{L_i/K})^{n_i}`
  for `V = Σ n_i Ind χ_i` rewrites `W ⊗ Ind χ_i` as `Ind (W|_{L_i} ⊗ χ_i)`
  before applying induction in degree zero. The same step is used in §4.8.
  The common-closure form above is the version needed there, with the test
  representation `W` as the left tensor factor, as in the target's
  `ExactWitness`.
