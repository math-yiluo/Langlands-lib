# The standard compact subgroup of the actual adelic `GL(n)` and bounded factors

This module defines the standard compact subgroup `K` of the actual adelic group
`AdelicGL F n = GL(n, 𝔸_F)` and proves that it is compact. It then proves that the
inverse of every bounded unimodular adelic matrix (`IsBoundedUnimodular`, from
`Langlands.Global.PrimitiveAdelicGLn`) factors as `β κ`, with `κ ∈ K` and `β` upper
triangular, equal to the identity at the finite places and with diagonal entries of
controlled norm at the infinite places. Here `F : Type u` is an arbitrary number field and
`n : ℕ` is arbitrary, including `n = 0`. The adele ring is the full
`Adeles F = AdeleRing (𝓞 F) F` with its actual topology. Norms at infinite places are the
norms of the completions `w.Completion`, and norms at finite places are those of the
completions `FiniteCompletion F v`, as in `PrimitiveAdelicGLn`.

The factorization is the step of the project's `GL(n)` Siegel-shape route that turns the
bounded factor `k` of `exists_reduction_GL` into an element of `K` times a triangular
matrix.

## Provenance

The statements are derived. Springer, *Reduction theory over global fields* (1994),
registered as `springer-1994-reduction-global-fields`, SHA256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`, §2.1 (printed p.211,
PDF p.5), deduces from the compactness of `G(A)/P(A)` that "there is a compact subset `K` of
`G(A)`" with `G(A)⁰ = K.(S(A) ∩ G(A)⁰).P(A)⁰`. Springer gives no explicit compact set.

For `GL(n)`, this module uses an explicit compact subgroup instead: the product of the
Library's `standardInfiniteCompact` and `FiniteAdelicGL.standardIntegral`. In place of the
compactness of `G(A)/P(A)` it proves the factorization directly. At the infinite places it
uses the triangular–unitary factorization `M = b u` of the Library-candidate module
`Langlands.LinearAlgebra.TriangularUnitary` (accepted, bundled unchanged here). At the
finite places it uses an adjugate argument. This module formalizes no statement of the
paper. The definitions, the bounds and the form of the statements are internal to the
project's route.

## Local linear algebra

* `det_mem_of_forall_mem O hA`: for a subring `O` of a field `K` and a square matrix `A`
  over `K` with all entries in `O`, `A.det ∈ O`.
* `adjugate_mem_of_forall_mem O hA i j`: under the same hypothesis, every entry of
  `A.adjugate` lies in `O`.
* `inv_mem_of_forall_mem O hA hdet i j`: if moreover `A.det⁻¹ ∈ O`, every entry of `A⁻¹`
  lies in `O`. This uses `A⁻¹ = (det A)⁻¹ • adjugate A`.
* `diag_bounds_of_isTriangularUnitaryFactorization hf hB hinv hdet i`: over `RCLike 𝕜`,
  let `M = b u` be a triangular–unitary factorization (`IsTriangularUnitaryFactorization M
  b u`: `b` upper triangular, `u` unitary). Suppose `1 ≤ B`, every entry of `M⁻¹` has norm
  at most `B`, and `‖det M‖ = 1`. Then
  `(√n · B)⁻¹ ≤ ‖b i i‖ ≤ (√n · B)ⁿ` for every `i`. The lower bound is the TriangularUnitary
  bound. The upper bound follows from `∏ⱼ ‖b j j‖ = ‖det b‖ = ‖det M‖ = 1` and the lower
  bounds on the other `n - 1` diagonal entries.
* `mul_inv_val_eq hf hU`: if `M = b u` as above and `U` is an invertible matrix with value
  `u`, then `M U⁻¹ = b`.

## The standard compact subgroup

* `standardCompact F n : Subgroup (AdelicGL F n)` is the set of `g` whose infinite
  component `AdelicGL.infinite F n g` lies in `standardInfiniteCompact F n` and whose finite
  component `AdelicGL.finite F n g` lies in `FiniteAdelicGL.standardIntegral F n`. The first
  of these is the Library's subgroup that is real orthogonal at each real place and complex
  unitary at each complex place, in completion coordinates. The second is the Library's
  subgroup of finite adelic matrices `g` such that `g` and `g⁻¹` have all entries in the
  local integer rings `v.adicCompletionIntegers F`.
* `mem_standardCompact_iff`: the membership condition above, by definition.
* `isCompact_standardCompact F n`: `standardCompact F n` is compact. It is the preimage of
  a product of two compact sets under the homeomorphism `AdelicGL.split F n` of
  `GL(n, 𝔸_F)` with the product of its infinite and finite parts. The two compactness
  inputs are the Library theorems `isCompact_standardInfiniteCompact` and
  `FiniteAdelicGL.standardIntegralCompact`.

## Finite places

* `finite_inv_mem_standardIntegral F n hk`: if `k` is bounded unimodular with any bound `B`,
  then `AdelicGL.finite F n k⁻¹ ∈ FiniteAdelicGL.standardIntegral F n`. At each finite place
  the entries of `k` have norm at most `1` and `det k` has norm `1`, so these entries and
  `(det k)⁻¹` are local integers. Then `inv_mem_of_forall_mem` makes the entries of `k⁻¹`
  local integers.

## Infinite places

* `realCoord v` and `complexCoord v` are the ring homomorphisms from the mixed space
  `NumberField.mixedEmbedding.mixedSpace F` to `ℝ` and `ℂ` that evaluate at a real place
  `v`, respectively at a complex place `v`.
* `norm_realCoord`, `norm_complexCoord`: transported through
  `InfiniteAdeleRing.ringEquiv_mixedSpace`, these coordinates preserve the norm of the
  completion at the place.
* `local_bounds φ w hφ h hinv hdet`: let `φ` be a coordinate that computes the norm at the
  infinite place `w`. Suppose the entries of `h⁻¹` at `w` have norm at most `B` and
  `‖(det h) w‖ = 1`. Then the same bounds hold for the matrix of `h` in the coordinate `φ`
  (via `archimedeanGLCoordinates`).
* `local_mul_inv φ h κ`: the coordinate matrix of `h κ⁻¹` is the coordinate matrix of `h`
  times the inverse of that of `κ`.
* `exists_infinite_factorization hB h hinv hdet`: let `1 ≤ B`, and let `h` be an infinite
  adelic invertible matrix such that at every infinite place `w` the entries of `h⁻¹` have
  norm at most `B` and `‖(det h) w‖ = 1`. Then `h = β κ` with
  `κ ∈ standardInfiniteCompact F n`, `β` upper triangular, and
  `(√n · B)⁻¹ ≤ ‖β i i w‖ ≤ (√n · B)ⁿ` for every infinite place `w` and every `i`. The
  matrix `κ` is assembled from the unitary factors of
  `exists_upperTriangular_mul_unitary` at each real and each complex place, and
  `β = h κ⁻¹`.

## Bounded unimodular matrices

* `exists_upperTriangular_mul_mem_standardCompact F n hB hk`: let `1 ≤ B` and let `k` be
  bounded unimodular with bound `B`. Then there are `β κ : AdelicGL F n` with
  * `k⁻¹ = β * κ`;
  * `κ ∈ standardCompact F n`;
  * `β` upper triangular (`β.val.IsUpperTriangular`);
  * `AdelicGL.finite F n β = 1`;
  * `(√n · B)⁻¹ ≤ ‖infiniteProjection F w (β i i)‖ ≤ (√n · B)ⁿ` for every infinite place
    `w` and every `i`.

  The infinite part of `k⁻¹` satisfies the hypotheses of `exists_infinite_factorization`:
  its inverse is the infinite part of `k`, and its determinant has norm `1` at each infinite
  place. Write that infinite part as `β₀ κ₀`. Then `β = (β₀, 1)` and
  `κ = (κ₀, finite part of k⁻¹)`. The finite part of `κ` lies in `standardIntegral` by
  `finite_inv_mem_standardIntegral`.

Nothing is asserted about uniqueness of the factorization or about `K` being maximal
compact. No Iwasawa decomposition of all of `GL(n, 𝔸_F)` is stated. The result covers only
inverses of bounded unimodular matrices.
