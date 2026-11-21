# Injectivity of weakly holomorphic finite frames

Module `Langlands.Analysis.Meromorphic.FiniteFrameInjectivity`. This is
internal infrastructure for the final finite-type argument of Bernstein–Lapid
§7.6: after smoothing a finite-dimensional family of vectors, one can shrink
the parameter neighbourhood to keep the smoothed operators injective.
The module does not construct the smoothing operators or prove local finiteness
of the adelic system.

## Continuous left inverse

Let `V` be a complex vector space with a topology and with separating
continuous complex dual (`SeparatingDual ℂ V`). For an injective continuous
linear map `L : ℂⁿ → V`, `exists_finiteFrameLeftInverse` gives a continuous
linear `Q : V → ℂⁿ` with `Q (L x) = x` for every `x`. The map
`finiteFrameLeftInverse L hL` chooses such a `Q`.

The proof sends a vector to its tuple of values under all continuous complex
linear forms on `V`. This is a continuous linear injection into a space of
complex functions with the topology of pointwise convergence. The images of
the coordinate basis under the composite with `L` are linearly independent.
`exists_continuousLinearMap_leftInverse` from `FiniteDimensionalValues`
constructs an inverse on their span which is defined and continuous on the
whole function space. Compose it with the evaluation map on `V`.

## Holomorphic families

- `IsHolomorphicOperatorFamilyOn.sum_smul_comp` takes a weakly holomorphic
  operator family `A(s) : B → V`, finitely many fixed continuous linear maps
  `Lⱼ : V → W`, and holomorphic scalar coefficients `cⱼ(s)` on the same set.
  With continuous addition, negation and multiplication by each fixed scalar
  in `W`, the family `∑ⱼ cⱼ(s) · (Lⱼ ∘ A(s))` is weakly holomorphic. After
  applying a scalar linear form `φ` on `W` to the value at `x ∈ B`, each term
  is a product of `cⱼ(s)` and the scalar test of `A(s)x` against `φ ∘ Lⱼ`.
- `IsHolomorphicOperatorFamilyOn.eventually_injective` takes a weakly
  holomorphic family `A(s) : ℂⁿ → V` on a set `U`, with `s₀ ∈ U` and
  `A(s₀)` injective. If the continuous dual of `V` separates points, `A(s)`
  is injective near `s₀` relative to `U`. Choose a continuous linear left
  inverse `Q` of `A(s₀)`. The entries of the matrix of `Q ∘ A(s)` are
  continuous within `U` at `s₀` by weak holomorphy. The matrix is the
  identity at `s₀`, hence its determinant is nonzero nearby. This gives
  injectivity of the composite, and therefore of `A(s)`. There is no
  assumption of continuity of `A` in an operator norm.
- `IsHolomorphicOperatorFamilyOn.exists_open_finiteTypeOn`: if `U` is open
  and a set `S(s)` is contained in the range of `A(s)` for every `s ∈ U`,
  then at such an `s₀` the same family witnesses `IsFiniteTypeOn` for `S`
  on some open neighbourhood of `s₀` contained in `U`.
