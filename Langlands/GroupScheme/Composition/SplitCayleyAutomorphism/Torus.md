# The rank-two torus of the split Cayley automorphism group scheme and its weights

Notation as in `Points.md` and `Maps.md`: `Aut` is the automorphism group scheme of Zorn's split
Cayley algebra over a field `K`. `𝕋` is the published rank-two split torus
`splitTorus.commGroupScheme (Spec K) (ULift (Fin 2))`, and `torusMap K : 𝕋 ⟶ Aut` is the torus
map. On points it sends `(s, t)` to the diagonal matrix
`torusGL s t = diag(1, s, t, (st)⁻¹, s⁻¹, t⁻¹, st, 1)`.

## Weights

- `weightCoord : Fin 8 → Fin 2 → ℤ` gives the weight of each of the eight coordinates in the
  torus coordinates `(s, t)`. The weights are `0, (1,0), (0,1), (-1,-1), (-1,0), (0,-1), (1,1), 0`.
  In other words, `torusGL s t` scales coordinate `i` by `s ^ w(i)₀ * t ^ w(i)₁`
  (`torusEntries_eq_prod`, `torusEntries_mulSingle`, `prod_zpow_weightCoord_sub`).
- `rootWeight : Root → Fin 2 → ℤ` gives the weight of each of the twelve roots. The short roots
  are `u1, u2, u3 ↦ (1,0), (0,1), (-1,-1)` and `v1, v2, v3 ↦ (-1,0), (0,-1), (1,1)`. The long
  roots are `l12, l13, l21, l23, l31, l32 ↦ (1,-1), (2,1), (-1,1), (1,2), (-2,-1), (-1,-2)`.
  `rootWeight_ne_zero` states that no root weight is zero.
- `rootDer_support`: every nonzero entry `(p, q)` of the root derivation matrix `X_α`, over any
  commutative ring, satisfies `w(p) - w(q) = rootWeight α`. The proof checks this over `ℤ` by
  `decide` (`rootDer_int_support`). It then transports the result along `ℤ → A`
  (`map_rootDerFun'`, a universe-general form of `map_rootDerFun` from `Smooth.lean`).
- `rootDerFun_unit`, `torusDerFun_unit`: root and torus derivations kill the unit `1`.
  `torusDer_zero`: `torusDer 0 0 = 0`.
- `eq_zero_of_pivots`: let `D` be a derivation matrix. Suppose its twelve pivot entries vanish:
  `D₁₀, D₂₀, D₃₀, D₃₅, D₁₆, D₂₄, D₁₂, D₁₃, D₂₁, D₂₃, D₃₁, D₃₂`, one coefficient for each root.
  Suppose also that its two diagonal entries `D₁₁, D₂₂` vanish. Then `D = 0`. This follows from
  the decomposition `D = derivCombination D` (`eq_derivCombination`, `Derivations.md`).

## The torus as a closed split torus

- `isSplitTorus_torus K`: `𝕋` is a split torus.
- `isClosedSubgroup_torusMap K`: `torusMap K` is a closed subgroup. A monomorphism out of a
  torus is a closed subgroup (`IsTorus.isClosedSubgroup_of_mono`), and `torusMap K` is a
  monomorphism (`mono_torusMap`, `Maps.md`).

## Weight spaces of the Lie algebra

Let `X` be an element of the Lie algebra of `Aut` over `K`, with coordinate matrix `lieMatrix X`.
Let `χ` be a character of `𝕋`, with integer coordinates `characterCoordEquiv (Fin 2) K χ`.

- `characterValue_eq_prod`: in coordinates, the value of `χ` on an affine point `t` of `𝕋` is
  `∏_c t_c ^ χ_c`.
- `mem_weightSpace_torusMap_iff`: `X` lies in the weight space of `χ` if and only if, for every
  `K`-algebra `A`, every affine point `t` of `𝕋` and every entry `(p, q)`,
  `t_p · X_pq · t_q⁻¹ = χ(t) · X_pq`. Here `t_i` is the `i`-th diagonal entry of `torusGL`.
  The proof uses the published criterion `lieKernelHomLinear_mem_weightSpace_iff` along the
  inclusion `Aut ⟶ GL₈`, together with the adjoint action on `GL₈`.
- `mem_weightSpace_torusMap_iff_support`: `X` lies in the weight space of `χ` if and only if
  every nonzero entry `(p, q)` of `lieMatrix X` satisfies `χ = w(p) - w(q)`. For the forward
  direction, evaluate on the Laurent-polynomial point `Pi.mulSingle c T` and compare exponents of
  `T` (`GeneralLinear.exponent_eq_of_C_mul_T`).

## The zero weight space and maximality

- `mem_weightSpace_zero_iff`: `X` has weight `0` if and only if `w(p) = w(q)` at every nonzero
  entry of `lieMatrix X`.
- `lieMatrix_eq_torusDer_of_mem_zero`: if `X` has weight `0`, then
  `lieMatrix X = torusDer (X₁₁) (X₂₂)`. All twelve pivot entries join coordinates of different
  weights, so the decomposition `eq_derivCombination` leaves only the torus part.
- `zeroIdx = ![1, 2]`. `zeroWeightCoord K` is the `K`-linear map from the zero weight space to
  `K²` reading off the diagonal entries `X₁₁, X₂₂`. `zeroWeightCoord_bijective` proves it is
  bijective. Injectivity uses the previous lemma. Surjectivity holds because every
  `torusDer a b` is a derivation killing `1`, so `exists_lieMatrix_eq` (`Points.md`) gives a Lie
  element with that matrix, and that element has weight `0`.
- `finrank_weightSpace_zero`: the zero weight space has dimension `2` over `K`.
- `isMaximalTorus_torusMap K`: **assume** the underlying space of `Aut` is connected (a
  `ConnectedSpace` instance hypothesis, proved separately). Then `torusMap K` is a maximal torus.
  This uses the published criterion `isMaximalTorus_of_finrank_zeroWeight`. Its hypotheses are:
  `Aut` is smooth (`smooth_automorphismGroup`, `Smooth.md`), affine and connected; `𝕋` is a
  closed split torus; and the zero weight space has the same dimension as the torus's own Lie
  algebra (`splitTorus.finrank_lieKernel`, which is `2`).

## Roots

- `rootChar K α` is the character of `𝕋` with coordinates `rootWeight α`.
  `characterCoordEquiv_rootChar` recovers these coordinates. `rootChar_injective` holds because
  the twelve weights are distinct.
- `exists_lieMatrix_eq_rootDer`: each root derivation `X_α` is the matrix of a Lie element of
  `Aut` over `K`. `mem_weightSpace_rootChar_of_lieMatrix_eq` puts that element in the weight
  space of `rootChar K α`, by `rootDer_support`.
- `pivot α` is the pivot entry of `X_α`, and `rootDer_pivot` states that `X_α` has entry `1`
  there, so `X_α ≠ 0` over a nontrivial ring (`rootDer_ne_zero`).
- `rootChar_mem_roots α`: `rootChar K α` is a root of `torusMap K`. It is nonzero, and its weight
  space contains a nonzero element.
- `roots_torusMap`: **the roots of `torusMap K` are exactly the twelve characters `rootChar K α`.**
  Let `χ` be a root and `X ≠ 0` an element of its weight space. If `χ` is not one of the
  `rootChar K α`, every pivot entry of `lieMatrix X` vanishes. Each pivot entry has weight
  `rootWeight α` (checked by `decide`), so a nonzero pivot entry would force `χ = rootChar K α`.
  The diagonal entries vanish too, because `χ ≠ 0` and a diagonal entry has weight `0`. Then
  `eq_zero_of_pivots` and the injectivity of `lieMatrix` give `X = 0`, a contradiction.
