# Compatible norms on affine opens along a finite field-extension base change (proof)

The theorem
`Langlands.AlgebraicGeometry.Picard.finiteFieldExtensionAffineNorm` proves the
Library statement `FiniteFieldExtensionAffineNormStatement.{u}` from module
`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionAffineNormStatement`. Its
type is exactly that proposition. No hypothesis is added.

## What is proved

Let `K` and `L` be fields in universe `u` with `L / K` finite, let `X` be a scheme
and `p : X ⟶ Spec K` a morphism. Write `X_L` for the actual Mathlib pullback
`pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L)))` and `π` for its first
projection. For every affine open `U` of `X`, the proof gives a monoid
homomorphism `Nm U : Γ(X_L, π⁻¹ U) →* Γ(X, U)` with these properties:

1. Restriction along every inclusion `U ≤ V` of affine opens commutes with `Nm`.
2. `Nm U (π.app U g) = g ^ Module.finrank K L` for every `g ∈ Γ(X, U)`.
3. The basic open of `Nm U f` is the set of points `x ∈ U` such that every `y`
   with `π y = x` lies in the basic open of `f`. Both inclusions are proved.

The fields may have any characteristic. The extension may be separable,
inseparable or trivial. Nothing is assumed about `X` or `p`; two affine opens may
have a non-affine intersection, and clause 1 never uses intersections.

## The implemented proof

The proof reuses the affine helpers of the published module
`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNormProof` (namespace
`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNorm`). It does not reprove
their algebra and does not use the extension from affine opens to all opens. In
that module `bc K L` abbreviates `Spec.map (CommRingCat.ofHom (algebraMap K L))`,
so its `pullback p (bc K L)` is the pullback in the target statement.

- The norm is `Nm U := normAff L p (U : X.Opens)`. This is `Algebra.norm Γ(X, U)`
  on `Γ(X_L, π⁻¹ U)`, with the algebra structure given by `π.app U`.
- Clause 1 is `normAff_res L p V.2 U.2 hUV f`. Here `V.2` and `U.2` are the proofs
  that `V` and `U` are affine.
- Clause 2 is `normAff_app L p U.2 g`.
- Clause 3 is proved by `Set.ext`, one direction at a time.
  - If `x` lies in the basic open of `Nm U f`, then `x ∈ U` because a basic open
    of a section over `U` lies in `U` (`X.basicOpen_le`). The fibre condition is
    the forward direction of `mem_basicOpen_normAff L p U.2 f x hx`.
  - If `x ∈ U` and the fibre condition holds, then the reverse direction of
    `mem_basicOpen_normAff L p U.2 f x hx` puts `x` in the basic open of
    `Nm U f`.

The published lemma `mem_basicOpen_normAff` itself proves both directions at a
point of an affine open: through primes and contraction for one direction, and
through going-up for the other. See the companion Markdown of
`FiniteFieldExtensionNormProof` for those arguments.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The target is the affine-local form of the norm of degree `d` for a finite
morphism in Stacks Project Section 31.18 (tag 0BCX), applied to `π` with
`d = [L : K]`. The construction behind the reused helpers is the determinant
norm of Lemma 31.18.6 (registered source
`stacks-norms-field-ample-descent-2026-10-26`, file `0BCX.html`). This module only
restricts those published helpers to affine opens; it adds no new mathematics.
