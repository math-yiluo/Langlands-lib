# Level-wise input for unitarity of character-limit constituents

Internal helper for the proof of `Langlands.UnitaryCharacterLimitSubquotientsStatement`
(a derived form of Tadić 1986, Theorem 2.7(i)). The proof works one compact open level
`K` at a time with the Hecke corner `H_K = HeckeAlgebra.Corner μ K hK` acting on `K`-fixed
vectors through `Hecke.cornerAction` (module structure `Hecke.cornerModule`). This module
supplies the two level-wise facts it needs; they are elementary consequences of published
Library results and have no separate literature source.

## Trace positivity at a level

`trace_cornerAction_star_mul_self_nonneg`: let `G` be Hausdorff, locally compact and totally
disconnected, `μ` a Haar measure, `ρ` an admissible representation whose distribution
character `Character.distribution μ ρ hρ` is of positive type in the sense of
`Character.IsPositiveType` (nonnegative on every `f† * f`). Then for every compact open `K`
and every `a ∈ H_K`,

  `0 ≤ trace (cornerAction ρ (star a * a))` on `ρ^K`.

Proof: `CharacterSeparation.distribution_corner` rewrites the trace as the character at the
test function underlying `star a * a`; in the Hecke algebra the product is convolution and
`star` is `TestFunction.adjoint`, so this test function is literally
`convolution μ (adjoint f) f` with `f` the test function underlying `a`, and positive type
applies. Only the `Star` structure of the corner is used, which needs just a Haar measure.

## Corner-linear maps of fixed vectors

`cornerLinearMap μ K hK hρ hσ T`: for smooth `ρ`, `σ` and an intertwiner `T : ρ → σ`, the
restriction `fixedVectorsMap T K` regarded as an `H_K`-linear map
`ρ^K →ₗ[H_K] σ^K` for the corner module structures (both installed by `letI`). Linearity over
`H_K` is `Hecke.cornerAction_intertwiner`; the underlying function is `fixedVectorsMap T K`
(`cornerLinearMap_apply`, by `rfl`).

* `cornerLinearMap_injective`: injective when `T` is (`fixedVectorsMap_injective`).
* `cornerLinearMap_surjective`: surjective when `T` is and `K` is compact
  (`fixedVectorsMap_surjective_of_complexAlgebra`, averaging over `K`).

These maps turn an actual subquotient `τ` of `ρ`, realized as `C ↪ ρ`, `C ↠ τ`
(`SmoothRep.isSubquotient_iff_exists`), into `H_K`-module maps `C^K ↪ ρ^K` and `C^K ↠ τ^K`.
