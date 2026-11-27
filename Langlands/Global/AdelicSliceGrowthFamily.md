# Uniform slice growth and its stability under twisted differentiation

Module `Langlands.Global.AdelicSliceGrowthFamily`, namespace `Langlands.Global.AdelicGroupPoints`.

## Declarations

- `HasUniformSliceGrowth hsmooth Γ H e ψ`: the infinite slices of `ψ` are smooth, `ψ` is left
  invariant under the subgroup `Γ` of the actual adelic points, and for every list `v` of directions
  there is `C` with `‖D_v (ψ(·, b))(a)‖ ≤ C * H(a, b) ^ e` for all `a` and `b`. The exponent `e` is
  the same for all `v`.
- `IsIwasawaCompact.parameterDirectionalSection_zero`: at the parameter `0` the Library's twisted
  derivative `parameterDirectionalSection` is `sliceDerivative`. Proof: `m_P^0 = 1`.
- `IsIwasawaCompact.parameterDirectionalSection_eq_sliceDerivative`: for smooth height pairings and
  smooth slices,
  `parameterDirectionalSection λ X ψ = sliceDerivative X ψ + ψ * sliceDerivative X ⟨λ, H_P⟩`. This
  is the Library's `parameterDirectionalSection_eq_add` combined with the previous item.
- `parabolicQuotientSubgroup_le_range`: `U(𝔸) M(F)` lies in the image of `P(𝔸)`.
- `IsIwasawaCompact.hasUniformSliceGrowth_parameterDirectionalSection`: if the height pairings are
  smooth, `K` contains the infinite components of its elements, and `Γ` lies in the image of
  `P(𝔸)`, then `parameterDirectionalSection λ X` preserves `HasUniformSliceGrowth hsmooth Γ H e`.

## Proof of the stability

By the decomposition above, the slice at `b` of the twisted derivative is
`D_X s_b + s_b * D_X π_b`, where `s_b` and `π_b` are the slices of `ψ` and of the height pairing
`⟨λ, H_P⟩`. Smoothness follows from `contMDiff_groupDirectionalValue` and `contMDiff_mul_complex`.
Left invariance: for `γ = p(q) ∈ Γ`, `ψ(γ g) = ψ(g)` and `⟨λ, H_P(γ g)⟩ = ⟨λ, H_P(g)⟩ + ⟨λ, log_P q⟩`
(`height_map_mul`), so both slice derivatives are invariant by `sliceDerivative_mul_of_add_const`.
Bounds: `D_v (D_X s_b) = D_{X :: v} s_b` is bounded by `C * H ^ e`. The iterated derivatives of
`D_X π_b` are nonempty iterated derivatives of `π_b`, bounded uniformly by
`exists_bound_heightPairing_derivative`, so `exists_bound_listDirectionalDerivative_mul` bounds the
derivatives of the product by a constant times `H ^ e`; additivity combines the two terms.

## Provenance

Internal. The module is an ingredient of the Library's proof of the smoothness aspect of
Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995), II.1.6, Proposition (i),
printed pp. 87–88, whose own proof on p. 88 treats convergence through an integrated Eisenstein sum
and II.1.5 and does not discuss derivatives. Right derivatives of `φ_λ = φ m_P^λ` are again of the
form `ψ_λ` with `ψ` left invariant under `U(𝔸) M(F)` (`parameterDirectionalSection_eq_add`). The
predicate `HasUniformSliceGrowth` records one growth exponent for all derivatives of such a `ψ`, and
the stability theorem keeps that exponent along the twisted derivatives, so that one envelope
dominates every derivative of the intertwining integrand. The exponent comes from uniformly moderate
growth in the sense of I.2.3 (printed p. 25), derived for automorphic forms on `U(𝔸) M(k) \ G` at the
end of I.2.17 (printed pp. 38–39) from I.2.5, Lemma (a) (printed p. 27).
