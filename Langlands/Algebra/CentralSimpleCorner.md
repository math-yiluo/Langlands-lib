# Corner algebras of central simple algebras

Let `K` be a field and `A` a `K`-algebra. Let `e` be an idempotent of `A`
(`he : IsIdempotentElem e`). The corner `e A e` is Mathlib's ring
`IsIdempotentElem.Corner he`. Its elements are the `x : A` with `e * x = x` and
`x * e = x`, and its unit is `e`. The module gives this ring its `K`-algebra
structure and proves the classical fact that a corner of a central simple
algebra at a nonzero idempotent is central simple and has the same Brauer
class.

## The corner as a `K`-algebra

- `corner_smul_mem`: the corner is stable under scalars of `K`.
- Instances `cornerSMul`, `cornerModule` and `cornerAlgebra` make
  `he.Corner` a `K`-algebra with `c • x` computed in `A`. The module structure
  is transported along the injective additive inclusion `cornerAddHom`.
- `cornerInclusion K he : he.Corner →ₗ[K] A` is the inclusion. It is injective
  (`cornerInclusion_injective`) and multiplicative (`cornerInclusion_mul`). It
  sends `1` to `e` (`cornerInclusion_one`) and `algebraMap K he.Corner c` to
  `c • e` (`cornerInclusion_algebraMap`).
- `cornerFiniteDimensional`: the corner of a finite-dimensional algebra is
  finite-dimensional.

## The left ideal `A e`

`cornerLeftIdeal e` is the left ideal `{x | x * e = x}` of `A`, which equals
`A e` when `e` is idempotent. `cornerGenerator he` is `e` as an element of it.
Every `x` in it satisfies `x = x • e` (`smul_cornerGenerator`), so an
`A`-linear endomorphism `f` is determined by `f e`:
`(f x) = x * f e` (`endo_apply_eq`). The value `f e` lies in the corner
(`endo_generator_mem`). Conversely, right multiplication by a corner element
is an endomorphism (`cornerRightMul`). Together they give the `K`-algebra
equivalence

`cornerEndEquiv he : Module.End A (cornerLeftIdeal e) ≃ₐ[K] (he.Corner)ᵐᵒᵖ`.

It sends `f` to `f e`. Composition is reversed because
`(f ∘ g) e = (g e) * (f e)`.

## Wedderburn comparison

Assume that `A` is finite-dimensional and simple, and that `e ≠ 0`.

`exists_matrix_divisionRing_corner` produces one division `K`-algebra `D`
and positive integers `n`, `m` with `A ≃ₐ[K] Matrix (Fin n) (Fin n) D` and
`he.Corner ≃ₐ[K] Matrix (Fin m) (Fin m) D`. The proof:

1. `A` is Artinian (`IsArtinianRing.of_finite`). Mathlib's Wedderburn–Artin
   theorem `IsSimpleRing.exists_algEquiv_matrix_end_mulOpposite` gives a simple
   left ideal `I` and `A ≃ₐ[K] Matrix (Fin n) (Fin n) (Module.End A I)ᵐᵒᵖ`.
   Put `D = (Module.End A I)ᵐᵒᵖ`, a division ring by Schur's lemma.
2. Every module over the simple Artinian ring `A` is isotypic
   (`IsSimpleRing.isIsotypic`). Restricting along the inclusion of the left
   ideal `A e` into `A` shows that every simple submodule of `A e` is
   isomorphic to `I`. The left ideal is finite over `A` because it is
   finite-dimensional over `K`. So `IsIsotypicOfType.linearEquiv_fun` gives
   `A e ≃ₗ[A] (Fin m → I)`. Here `m ≠ 0` because `e` is a nonzero element of
   `A e`.
3. Then
   `he.Corner ≃ (he.Corner)ᵐᵒᵖᵐᵒᵖ ≃ (Module.End A (A e))ᵐᵒᵖ
   ≃ (Module.End A (Fin m → I))ᵐᵒᵖ ≃ (Matrix (Fin m) (Fin m) (Module.End A I))ᵐᵒᵖ
   ≃ Matrix (Fin m) (Fin m) D`.
   This uses `cornerEndEquiv`, `LinearEquiv.conjAlgEquiv`,
   `endVecAlgEquivMatrixEnd` and `AlgEquiv.mopMatrix`.

`exists_matrix_corner_algEquiv` then gives
`Matrix (Fin n) (Fin n) he.Corner ≃ₐ[K] Matrix (Fin m) (Fin m) A` with
`n, m ≠ 0`. Both sides are block matrices over `D` indexed by
`Fin n × Fin m` and `Fin m × Fin n` (`Matrix.compAlgEquiv`,
`Matrix.reindexAlgEquiv`).

Consequences:

- `isSimpleRing_corner`: the corner is a simple ring, since it is a matrix
  ring over a division ring.
- `isCentral_corner`: if `A` is central over `K`, so is the corner.
  `Matrix (Fin m) (Fin m) A` is central (Mathlib), hence so is the isomorphic
  `Matrix (Fin n) (Fin n) he.Corner`. The general lemma `isCentral_of_matrix`
  shows that `B` is central over `K` whenever `Matrix ι ι B` is, for nonempty
  `ι`. Its proof applies Mathlib's description of the center of a matrix
  algebra (`Matrix.subalgebraCenter_eq_scalarAlgHom_map`) to the scalar
  matrix of a central element of `B`.

## The corner CSA and its Brauer class

For `A : CSA.{u, v} K` (Mathlib's finite-dimensional central simple
algebras), `cornerCSA A he hne : CSA.{u, v} K` has carrier `he.Corner`.
`isBrauerEquivalent_cornerCSA` proves

`IsBrauerEquivalent (cornerCSA A he hne) A`,

with Mathlib's `IsBrauerEquivalent` (`Mₙ(eAe) ≃ₐ[K] Mₘ(A)` for some positive
`n`, `m`). `brauerClass_cornerCSA` states the same fact as equality of
classes in Mathlib's quotient `BrauerGroup.{u, v} K`. Its proof is
`Quotient.sound`.

No hypothesis on `K` (characteristic, perfectness, separable closure) is
used. The field and the algebra live in arbitrary universes `u`, `v`.

Provenance: internal, a standard fact (for example, Morita theory of
corners of a simple Artinian ring). The proof is the implemented reduction to
the Wedderburn–Artin theorem and isotypic decomposition already in Mathlib.
No external result beyond Mathlib is assumed.
