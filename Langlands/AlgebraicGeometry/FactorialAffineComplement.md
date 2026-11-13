# Complements of affine opens have codimension at most one at factorial points

Author: Worker 171.

Module `Langlands.AlgebraicGeometry.FactorialAffineComplement`, namespace
`Langlands.AlgebraicGeometry.FactorialAffineComplement`.

## Declarations

- `nonempty_top`: the top open of `Spec O` is nonempty for a domain `O` (it contains
  the generic point); needed to form the germ to the function field.
- `germToFunctionField_top_ΓSpecIso_inv`: for a domain `O` and `r : O`, the germ in
  the function field of the global function `(Scheme.ΓSpecIso O).inv r` is
  `algebraMap O (Spec O).functionField r` (definitional).
- `not_isAffineOpen_punctured`: let `O` be a local domain with
  `UniqueFactorizationMonoid O`, having a prime `q` with `q ≠ ⊥` and
  `q ≠ maximalIdeal O`. If an open `P` of `Spec O` consists exactly of the points
  different from the closed point, then `P` is not affine.
- `false_of_generization_chain`: let `X` be a separated scheme, `W` an affine open,
  and `z ∉ W` a point all of whose proper generizations lie in `W`. If the stalk at
  `z` is a domain with unique factorization, there are no points `y₀ ⤳ y₁ ⤳ z` with
  `y₀ ≠ y₁` and `y₁ ≠ z`.

## Proofs as implemented

`not_isAffineOpen_punctured`. If `P` were affine, the restrictions of the elements of
the maximal ideal would span the unit ideal of `Γ(Spec O, P)`, because their basic
opens cover `P` (`IsAffineOpen.self_le_iSup_basicOpen_iff`; every non-closed point
misses some element of the maximal ideal). On the other hand every section `c` on `P`
has a germ in the function field which, for each nonzero `f` in the maximal ideal,
becomes integral after multiplication by a power of `f`: restrict `c` to the basic
open `D(f) ⊆ P` and use `IsAffineOpen.isLocalization_basicOpen`. By
`FactorialLocalHartogs.exists_eq_of_forall_pow_mul` every germ comes from `O`. This
defines a ring homomorphism `Γ(Spec O, P) → O` that is the identity on restricted
elements of `O`; mapping the unit-ideal equation gives `1` in the maximal ideal, a
contradiction.

`false_of_generization_chain`. Pull back along `X.fromSpecStalk z`, an embedding with
range the generizations of `z`. The preimage of `W` is exactly the complement of the
closed point. It is affine because a morphism from an affine scheme to a separated
scheme is affine (`MorphismProperty.of_postcomp` with `IsSeparated`). The points
`y₁` and `y₀` give primes `p₀ < p₁` of the stalk with `p₁` not maximal, so
`not_isAffineOpen_punctured` applies.

## Provenance

This is the factorial case of the statement that the complement of an affine open
in a noetherian separated scheme has all components of codimension at most one
(EGA IV 21.12.7), as used in Lemma 3.4 of N. Guo, *Ample sheaves on group homogeneous
spaces over Prüfer bases*, arXiv 2209.02443v1, printed p.6 (registered source
`guo-ample-sheaves-prufer-2209-02443-v1`). The implemented proof is an internal
Hartogs argument for factorial local rings and does not use EGA.
