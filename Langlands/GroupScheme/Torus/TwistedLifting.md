# Lifting twisted transporters along nilpotent extensions

Let `F` be a group functor on commutative `R`-algebras, corepresented by `B` through `e`, and `ι` a `CharacterEmbedding`. For an `R`-algebra `C` and a grouplike family `s` over `C`, a point `g` of `F` over a `C`-algebra is a *twisted transporter* when `ι(twist s t) * g = g * ι(t)` for all characters `t`. The main theorem lifts twisted transporters along nilpotent ideals when `B` is formally smooth.

## Base change to `C`

- `baseRing C` is `C` as a commutative ring. `restrictScalars C D` views a `C`-algebra `D` as an `R`-algebra through `R → C → D`; `restrictScalarsMap` acts on morphisms. `toRestrict D : C ⟶ restrictScalars C D` is the structure map, and `toRestrict_comp` records its compatibility with morphisms.
- `restrictIso D₀` identifies the restriction of an `R`-algebra `D₀` that is also a compatible `C`-algebra with `D₀` itself; the underlying map is the identity.
- `baseChange C B` is `C ⊗[R] B` as a `C`-algebra. `baseChangeEquiv D` identifies its points over a `C`-algebra `D` with points of `B` over `restrictScalars C D` (Mathlib's `AlgHom.liftEquiv`), naturally in `D` (`baseChangeEquiv_comp`).
- `restrictChar` views a character over `D` as a character over its restriction. `basePoint e x` is the point of `F` over `restrictScalars C D` given by a point `x` of the base change. Its naturality is `basePoint_comp`, its inverse property is `basePoint_symm`, and its injectivity is `basePoint_injective`.

## The twisted action

`twistedAction e ι s hs` is an `Action` (in the published sense of `CharacterActionGrading`, over the base ring `C`) on `C ⊗[R] B`. It is given by `t · g = ι(twist s t) * g * ι(t)⁻¹` on points of `F` (`twistedAction_act`). Its laws are:

- the unit law, from `twist_one`;
- the composition law, from `twist_mul` and `(ab)⁻¹ = b⁻¹a⁻¹`;
- naturality, from naturality of `ι`, of the twist and of the base change.

No group law is used beyond `F`'s group structure, and no commutativity of `F` is needed.

## Fixed points

Fixed points are lifted by the published `CharacterAction.exists_fixed_lift` (module `Langlands.GroupScheme.Torus.FixedPointLifting`, by Worker 1296): a point fixed by a character action on a formally smooth algebra, after every refinement, lifts along a nilpotent ideal to a point with the same property. This module only builds the twisted action to which it is applied.

## Main results

- `twisted_of_universal`: the twisted transporter equation over all `C`-algebras follows from the single universal equation over `C[M]`, by applying `F.map (evaluate f t)`.
- `exists_twisted_lift`: suppose `B` is formally smooth over `R`, `N` is a nilpotent ideal of `C`, and `s` is a grouplike family over `C`. Let `g₀ ∈ F (C ⧸ N)` satisfy the twisted transporter equation after every refinement. Then there is `g ∈ F C` that reduces to `g₀` and satisfies the equation after every refinement.

  The proof transports `g₀` to a fixed point of `twistedAction` over the `C`-algebra `C ⧸ N`. Formal smoothness of `C ⊗[R] B` over `C` is Mathlib's base-change instance. The point is lifted by `exists_fixed_lift` and transported back. The universal fixedness equation over `C[M]` (as a `C`-algebra) gives the universal transporter equation.

## Provenance

This is an internal construction toward task `0f453442`. It formalizes the infinitesimal lifting step for transporters `{g | g i(t) g⁻¹ = i(σ t)}` between diagonalizable subgroups. In Milne, *Algebraic Groups* (2017), the corresponding geometric input is the smoothness of fixed-point schemes of diagonalizable groups (Theorem 13.1, used for Corollary 13.10). The implemented proof is the square-zero lifting argument of the published `GradedFixedQuotient`, applied after base change to the twisting ring.
