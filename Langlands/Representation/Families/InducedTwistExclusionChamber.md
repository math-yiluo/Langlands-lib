# Nonempty open coroot chambers

Author: Worker 5120.

This internal supporting module proves that the published open coroot chamber
`restrictedCorootChamber` (Renard V.3.15, `^G_P[𝔞*_M]^+`) is nonempty for a standard
simple-root index. It is used to obtain an unramified character whose real part lies in that
chamber, which is the hypothesis of the published nonidentity-piece displacement theorem.
It adds no literature assertion: it is a finite computation with the supplied integral
reflection data.

## Declarations

Namespace `Langlands.GroupScheme`. Fix a group scheme `G` with affine structure map, an
actual torus map `i : T → G` that is a monomorphism, integral reflection data
`D : RelativeRootReflectionData i`, and assume that the set of relative roots is finite.

- `sum_relativeRoots_weylAction`: for every normalizing point `n`, reindexing a finite sum over
  the relative roots by `weylAction i n` does not change it. The proof shows that the
  Weyl action maps the finite set of relative roots onto itself
  (`weylAction_image_relativeRoots`), so the image finset equals the original one.
- `two_mul_sum_pairing_coroot`: for every cocharacter `ζ` and relative root `α`,
  `2 ∑_β ⟨β, ζ⟩⟨β, α^∨⟩ = ⟨α, ζ⟩ ∑_β ⟨β, α^∨⟩²`, sums over the relative roots. Reindex the
  left sum by the reflection representative of `α`. The reflection formula
  `s_α β = β - ⟨β, α^∨⟩ α` and `⟨α, α^∨⟩ = 2` give `⟨s_α β, α^∨⟩ = -⟨β, α^∨⟩`. They also give
  `⟨s_α β, ζ⟩ = ⟨β, ζ⟩ - ⟨β, α^∨⟩⟨α, ζ⟩`. Adding the two expressions of the sum termwise
  gives the identity.
- `sum_pairing_coroot_sq_pos`: the sum `∑_β ⟨β, α^∨⟩²` is positive, since its term at `β = α`
  is `4` and all terms are nonnegative.
- `restrictedCorootChamber_nonempty`: if `ζ` is a standard cocharacter for `(ν, J)`
  (`IsStandardCocharacter`), the restriction along `f : A → T` of the real character
  `y = ∑_β ⟨β, ζ⟩ ⊗ β` lies in `restrictedCorootChamber i ν J f D`. By the identity above,
  `⟨y, α^∨⟩` has the sign of `⟨α, ζ⟩`. That is zero for `α ∈ J` and positive for simple roots
  outside `J`, as the chamber definition requires.
