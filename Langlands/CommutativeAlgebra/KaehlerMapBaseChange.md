# The first map of the first fundamental exact sequence of Kähler differentials

Module `Langlands.CommutativeAlgebra.KaehlerMapBaseChange`, namespace
`Langlands.CommutativeAlgebra.KaehlerMapBaseChange`. It imports only `Langlands.MathlibBase`.

For a tower of commutative rings `R → A → B`, Mathlib's `KaehlerDifferential.mapBaseChange R A B :
B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` is the first map of the exact sequence
`B ⊗[A] Ω[A⁄R] → Ω[B⁄R] → Ω[B⁄A] → 0` (`KaehlerDifferential.exact_mapBaseChange_map`; Matsumura,
*Commutative Ring Theory*, Thm. 25.1). This module records its cokernel, a criterion for its
injectivity, and the cokernel when both sides are of rank one. These are the algebraic inputs for
the map `f^*Ω¹_{X/κ} → Ω¹_{Y/κ}` of a finite morphism of curves (Serre, *Local Fields*, III §7,
Prop. 14; Hartshorne, *Algebraic Geometry*, IV.2.1).

| Declaration | Statement |
|---|---|
| `quotRangeMapBaseChangeEquiv R A B` | `(Ω[B⁄R] ⧸ range (mapBaseChange R A B)) ≃ₗ[B] Ω[B⁄A]` |
| `length_quot_range_mapBaseChange` | the cokernel of `mapBaseChange R A B` has the `B`-length of `Ω[B⁄A]` |
| `length_quot_range_mapBaseChange_eq_zero` | if `A → B` is formally unramified, the cokernel has length `0` |
| `map_map_apply` | for a tower `A → B → L` over `R`, `Ω[A⁄R] → Ω[B⁄R] → Ω[L⁄R]` is `Ω[A⁄R] → Ω[L⁄R]` |
| `mapBaseChange_injective` | if `Ω[A⁄R]` is flat over `A`, `L` is a formally étale `A`-algebra and `B → L` is injective (for compatible towers), then `mapBaseChange R A B` is injective |
| `quotRangeMapBaseChangeEquivOfSpan` | if `ω` spans `Ω[A⁄R]` over `A`, `e : B ≃ₗ[B] Ω[B⁄R]` and the image of `ω` in `Ω[B⁄R]` is `c • e 1`, then the cokernel is `B ⧸ (c)` |
| `length_quot_range_mapBaseChange_eq_ord` | in the same situation the cokernel has length `Ring.ord B c` |

## Proofs

`quotRangeMapBaseChangeEquiv`: the range of `mapBaseChange R A B` is the kernel of the surjection
`KaehlerDifferential.map R A B B : Ω[B⁄R] → Ω[B⁄A]` (`KaehlerDifferential.range_mapBaseChange`,
`KaehlerDifferential.map_surjective`), and `LinearMap.quotKerEquivOfSurjective` identifies the
quotient. For a formally unramified `A → B`, `Ω[B⁄A]` is zero
(`Algebra.FormallyUnramified`), hence of length `0`.

`map_map_apply`: both sides are `A`-linear in `ω` and agree on the generators `D a`
(`KaehlerDifferential.map_D`), which span `Ω[A⁄R]`.

`mapBaseChange_injective`: with `T = rTensor (B → L) : B ⊗[A] Ω[A⁄R] → L ⊗[A] Ω[A⁄R]`, the square
`mapBaseChange R A L ∘ T = map R R B L ∘ mapBaseChange R A B` commutes (on pure tensors by
`map_map_apply`). `T` is injective because `Ω[A⁄R]` is flat
(`Module.Flat.rTensor_preserves_injective_linearMap`), and `mapBaseChange R A L` is the
isomorphism `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A L`. Hence
`mapBaseChange R A B` is injective.

`quotRangeMapBaseChangeEquivOfSpan`: every element of `Ω[A⁄R]` is `a • ω`, so the range of
`mapBaseChange R A B` is the `B`-span of `c • e 1`, which is the image under `e` of the ideal
`(c)`; `Submodule.Quotient.equiv` gives the isomorphism, and `Ring.ord B c` is by definition the
length of `B ⧸ (c)`.
