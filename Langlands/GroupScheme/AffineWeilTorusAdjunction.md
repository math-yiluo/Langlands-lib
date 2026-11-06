# Character functors and the Weil restriction point functor

Author: Worker 112.

Fix commutative rings `A` and `B`, an `A`-algebra structure on `B`, and a group
scheme `G` over `Spec B`. The published `AffineWeil.pointFunctor A B G` sends an
`A`-algebra `C` to the `G`-points over `B ⊗[A] C`. It needs no further
hypotheses, and every construction in this file works with it at this
generality. When `Module.Finite A B`, `Module.Projective A B`,
`IsAffine G.X.left` and `LocallyOfFiniteType G.X.hom` hold, the published
`AffineWeil.groupScheme A B G` is the actual Weil restriction, and the published
`AffineWeil.pointsEquiv` identifies its affine points with this point functor.
This file does not use the finiteness and projectivity hypotheses. Affineness of
`G` is assumed only in the lifting and counit centrality results below.

For an abelian group `Λ` and a ring `R`, the published `latticeFunctor R Λ`
sends an `R`-algebra `C` to the characters `Λ → Cˣ`. For general `Λ` this is the
point functor of the diagonalizable group `D(Λ)`, which need not be a torus: for
`Λ = ℤ/2` over `ℚ` it is `μ₂`. When `Λ` is a finite free abelian group, as
in the intended lattice applications, it is a split torus. The definitions below
keep the general `Λ`.

This file exchanges natural homomorphisms from `latticeFunctor A Λ` into
`AffineWeil.pointFunctor A B G` with natural homomorphisms from
`latticeFunctor B Λ` into the affine-point functor `G.affinePointFunctor`. It
also shows that both directions preserve centrality, given the hypotheses
stated below.

## Restriction of scalars and multiplication

- `restrictScalars A B` is the functor from `B`-algebras to `A`-algebras that
  keeps the ring and makes it an `A`-algebra through `A → B`
  (`Algebra.compHom`).
- `multiplication A C : B ⊗[A] C → C`, for a `B`-algebra `C`, is the map
  `b ⊗ c ↦ b · c` (`multiplication_tmul`). It is a map of `B`-algebras.
- `multiplication_naturality`: the multiplication maps are natural in `C`.
  `multiplication_tensorMap_tmul` evaluates the multiplication after tensoring a
  map into a restricted algebra.

## Lifting through the multiplication map

This section assumes `Algebra.FormallyUnramified A B` and
`Algebra.EssFiniteType A B`. A finite separable field extension satisfies both.
Let `C` be an `A`-algebra and a `B`-algebra with a compatible scalar tower, and
let `tensorMul A B C : B ⊗[A] C → C` be the multiplication.

- Mathlib's `Algebra.FormallyUnramified.elem A B` is an element `t` of
  `B ⊗[A] B`. It satisfies `(1 ⊗ s - s ⊗ 1) t = 0` for all `s`, and its product
  is `1`.
- `mul_elem_eq` shows `u t = (lmul' u ⊗ 1) t`. Hence `elem_mul_elem`: `t` is
  idempotent.
- `sepIdempotent A B C` is the image `e` of `t` in `B ⊗[A] C`. It is idempotent
  (`sepIdempotent_mul_self`), its multiplication image is `1`
  (`tensorMul_sepIdempotent`, from `tensorMul_map`), and it absorbs the
  difference of the two `B`-actions (`one_tmul_mul_sepIdempotent`).
- `exists_tensorMul_comp_eq`: let `O` be a `B`-algebra and suppose some
  auxiliary `B`-algebra map `z : O → B ⊗[A] C` is given. Then every `B`-algebra
  map `f : O → C` lifts to a `B`-algebra map `f' : O → B ⊗[A] C` with
  `tensorMul ∘ f' = f`. The lift is `f'(o) = e (1 ⊗ f(o)) + (1 - e) z(o)`. For
  points of `G`, `z` is the identity point.
- `exists_affinePointMap_multiplication_eq`: for an affine `G`, every `G`-point
  over a `B`-algebra `C` is the image of a `G`-point over `B ⊗[A] C` under the
  multiplication map. This uses the existing comparison between affine points
  and global-section algebra maps.

## Natural homomorphisms

- `latticeRestrict A B Λ` identifies `B`-valued characters with characters
  valued in the restricted algebra.
- `multiplicationTrans A G` applies the multiplication map to points of `G`.
- `counitTrans A G α` is defined for
  `α : latticeFunctor A Λ ⟶ AffineWeil.pointFunctor A B G`. It is the natural
  homomorphism `latticeFunctor B Λ ⟶ G.affinePointFunctor` that evaluates `α`
  on the restricted algebra and then multiplies (`counitTrans_app`).
  `affinePointMap_multiplication_app` and
  `affinePointMap_tensorMap_multiplication` express the naturality used to
  compute it.
- `latticeUnit A B` sends a character `Λ → Cˣ` to `Λ → (B ⊗[A] C)ˣ` through
  `c ↦ 1 ⊗ c`.
- `unitTrans A G I` is defined for
  `I : latticeFunctor B Λ ⟶ G.affinePointFunctor`. It is the natural
  homomorphism `latticeFunctor A Λ ⟶ AffineWeil.pointFunctor A B G` given by
  `χ ↦ I(1 ⊗ χ)` (`unitTrans_app`).

## Centrality

Centrality uses the published `IsCentralNat`: every value commutes with every
point of the target functor.

- `isCentralNat_unitTrans`: if `I` is central, then `unitTrans A G I` is
  central. The values of `AffineWeil.pointFunctor A B G` over `C` are exactly
  the `G`-points over `B ⊗[A] C`.
- `isCentralNat_counitTrans`: let `G` be affine and let `A → B` be formally
  unramified and essentially of finite type. If `α` is central, then
  `counitTrans A G α` is central. This uses the lifting result above.

## Provenance and scope

The restriction-of-scalars adjunction on points is standard Weil-restriction
theory. This file is an internal construction on the published Library
`AffineWeil.pointFunctor`, `latticeFunctor` and `IsCentralNat`. The
separability-idempotent argument is the usual one for unramified algebras. Its algebraic input is Mathlib's element
`Algebra.FormallyUnramified.elem` with `one_tmul_mul_elem` and `lmul_elem`
(from `Mathlib.RingTheory.Unramified.Finite`). The file does not show
that the two constructions are mutually inverse, and it asserts nothing about
split components or adelic points.
