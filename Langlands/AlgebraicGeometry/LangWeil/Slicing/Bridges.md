# Ring-level forms of the Lang–Weil estimate and of the point-count upper bound

Author: Worker 5132.

This helper module specializes the scheme-level statements `FamilyLangWeilInDimension e` and
`FamilyPointUpperBoundStatement` to the morphism `Spec B ⟶ Spec R`. Here `B` is an algebra of
finite type over a ring `R` of finite type over `ℤ`. Points and fibre conditions are expressed
through algebra homomorphisms and tensor products. The hyperplane-slicing proof uses it for
`FamilyLangWeilSlicingStatement`.

## Provenance

Provenance: internal. The module only translates between the scheme-level formulation of the
Library statements (see their Markdown in
`Langlands/AlgebraicGeometry/LangWeil/FamilyLangWeilStatement.md` and
`FamilyPointUpperBoundStatement.md`) and commutative algebra. It adds no mathematics from the
literature.

## Declarations

- `natCard_specPoints_eq R B κ`: the `κ`-points of `Spec B` lying over the `κ`-point of `Spec R`
  given by `algebraMap R κ` correspond to the `R`-algebra homomorphisms `B →ₐ[R] κ`. Proof:
  Mathlib's `Spec.homEquivAlgHom`.
- `locallyOfFiniteType_specULiftZ R` and `locallyOfFiniteType_specMap R B`: `Spec R` is locally
  of finite type over the terminal scheme `Spec (ULift ℤ)` when `R` is of finite type over `ℤ`,
  and `Spec B ⟶ Spec R` is locally of finite type when `B` is of finite type over `R`. Proof:
  `HasRingHomProperty.Spec_iff` for `LocallyOfFiniteType`. In the first case the morphism to the
  terminal object is identified with `Spec` of `ULift ℤ ≃+* ℤ → R`.
- `topologicalKrullDim_fiber_specMap R B κ`: for a field `κ` over `R`, the fibre of
  `Spec B ⟶ Spec R` over the image of the closed point of `Spec κ` has the Krull dimension of
  `p.Fiber B = κ(p) ⊗[R] B`, where `p = ker (R → κ)`. Proof: the Library's
  `specFiberTensorIso` (the actual fibre is `Spec (κ(p) ⊗[R] B)`) and
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`.
- `langWeil_ring hLW R B hgi hdim`: assume `FamilyLangWeilInDimension e`. If `K ⊗[R] B` has prime
  nilradical for every field `K` over `R`, and every residue-field fibre ring `p.Fiber B` has
  pure dimension `e`, then there is `C > 0` with
  `|#(B →ₐ[R] κ) - (#κ)^e| ≤ C (#κ)^(e - 1/2)` for every finite field `κ` and every `R`-algebra
  structure on it. Proof: apply the hypothesis to `Spec B ⟶ Spec R`. Geometric irreducibility
  comes from the Library's `geometricallyIrreducible_specMap_iff`, pure fibre dimension from
  `hasPureDimension_specFiber_iff`, and points are counted by `natCard_specPoints_eq`.
- `upperBound_ring hUB R B`: given `FamilyPointUpperBoundStatement`, there is `C > 0` such that
  `#(B →ₐ[R] κ) ≤ C (#κ)^e` for every finite field `κ` over `R` and every `e` bounding the
  dimension of `p.Fiber B` at `p = ker (R → κ)`. Proof: apply the hypothesis to
  `Spec B ⟶ Spec R`, using `topologicalKrullDim_fiber_specMap` for the fibre dimension.
