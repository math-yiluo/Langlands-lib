# Unramified base-change Satake parameters of Kottwitz's unitary similitude groups

Author: Worker 8. Module `Langlands.Shimura.Unitary.KottwitzBaseChange`, namespace
`Langlands.Shimura.KottwitzUnramified`. This is item 4 of Task 5424. It builds on the
standard unramified charts of `KottwitzChart` (item 1) and on the principal-series
parameters, normalized position values and Weyl equivalence of
`KottwitzPrincipalSeries` (item 2).

For a place `w` of the CM field `K` above a good prime `p`, the module defines the Satake
parameter at `w` of the unramified base change of an unramified representation `π_p` of
`G(ℚ_p)` to `GL_n(K_w)`. It is a multiset of `n` units. For complex coefficients it is
an element of the published `Langlands.Unramified.Eigenvalues n`. The module proves that
the parameter depends only on the Weyl-equivalence class of the principal-series
parameter. It also proves the conjugate self-duality `t_{w̄} = t_w^{-1}`. It records
Clozel's normalization and states the comparison with the Hecke eigenvalues of the
`GL_n(K_w)` factor at split places.

## Sources

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math.
  Kyoto Univ. 39 (1999), source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, Theorem 5.7(ii),
  printed p.313 (PDF p.15). For almost all places `w` of `𝒦` dividing rational primes
  `p` at which `π` is unramified, the normalized local Artin `L`-function of `ρ(π)` at
  `w` coincides with "the standard local Euler factor `L(s, BC_{𝒦/E}(π)_w)`. Here
  `BC_{𝒦/E}` denotes quadratic base change from automorphic representations of `GJ` to
  automorphic representations of `GL(n, 𝒦)`". Harris's `𝒦` is the CM field `K` here,
  and his `E` the totally real field `E` here. The local component `BC(π)_w` at an
  unramified place is the unramified representation of `GL_n(K_w)` whose Satake
  parameter this module defines, and `L(s, BC(π)_w) = Π_k (1 - t_k q_w^{-s})^{-1}`.
- Clozel, *Représentations galoisiennes associées aux représentations automorphes
  autoduales de GL(n)*, Publ. Math. IHÉS 73 (1991), source
  `clozel-1991-selfdual-galois`, SHA-256
  `9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac`, §5.1, printed
  p.131 (PDF p.36), checked visually. Formula (5.2), `r_v(𝓕_v) = t_{π,v}`, says that the
  Hecke matrix `t_{π,v}` is the image of a geometric Frobenius `𝓕_v` under the
  unramified Langlands parameter, with the reciprocity law normalized to send `𝓕_v` to
  a uniformizer `ϖ_v`. Formula (5.3) defines `r_v^T` by `r_v^T(𝓕_v) = q_v^{(1-n)/2} t_{π,v}`.
- The published `Langlands.Unramified.HasSphericalHeckeSpectrum`
  (`Representation/Unramified/HeckeOperators.lean`) fixes the Library's normalization of
  `GL_n` Satake parameters. The standard double-coset operator of `diag(ϖ^{(i)}, 1^{(n-i)})`
  acts on the spherical vectors by `√q^{i(n-i)} e_i(s)`, with `e_i` the elementary
  symmetric function (`elementaryCoefficient`). This is the unitary normalization
  `t_{π,v}` of Clozel's (5.2).

## Declarations

`c : UnramifiedChart σ p n` is a standard chart and `L` a field. `s : SqrtPrime p L` is a
square root of `p` in `L`. `ξ : T →* Lˣ` is a character of the torus. Positions are
`k : Fin n`, numbered from `0`.

- `symOfFn f : Sym α n` is the multiset of values of a family `f : Fin n → α`.
  `symOfFn_comp_perm` shows that it is invariant under permutations of `Fin n`, and
  `symOfFn_map` that it commutes with maps.
- `UnramifiedChart.baseChangeParameter s ξ w` is the multiset
  `{positionValue s ξ w k : k}` of the unitarily normalized values
  `ξ(λ_{w,k}(p)) · s^{f_w (n - 1 - 2k)}`. Here `λ_{w,k}` is the cocharacter with exponent
  `+1` at `(w, k)` and `-1` at `(w̄, rev k)`. Its point is `λ_{w,k}(p) = d θ(d)⁻¹`, for
  `d` the diagonal element with `p` at `(w, k)`, so it is the norm `N(d)` from the
  diagonal torus of `GL_n(K_w)` to the torus of `G` used by unramified base change. The
  base-change parameter is the unitarily normalized character `ξ δ_B^{-1/2} ∘ N` at the
  uniformizers of `K_w` (`p` is a uniformizer, since `K_w` is unramified). Only
  cocharacters with multiplier exponent `0` enter, so the similitude part of the
  parameter does not contribute. This matches Harris's base change from `GJ` to
  `GL(n, 𝒦)`, which goes through the unitary group.
- At a split place (`w̄ ≠ w`), the subgroup of `G(ℚ_p)` with coordinates `g` at `w`,
  `θ(g)⁻¹` at `w̄`, `1` elsewhere and multiplier `1` is the `GL_n(K_w)` factor. The
  `λ_{w,k}` are the diagonal cocharacters of this factor, and the base-change parameter
  is the unitarily normalized Satake parameter of the `GL_n(K_w)` factor (the
  `χ_k(ϖ_w)` of the normalized principal series `I(χ_1, …, χ_n)`). This is the
  convention of the published `GL_n` spectra.
- At an inert place (`w̄ = w`), `λ_{w, rev k} = -λ_{w,k}`, so the parameter is
  `{β_k^{±1}}` for the unitary parameters `β_k` (`k < rev k`), together with `1` at the
  middle position when `n` is odd. This is the standard unramified base change from the
  quasi-split unitary group to `GL_n(K_w)`.
- `baseChangeParameter_of_weylEquivalent`: Weyl-equivalent characters (item 2) have the
  same base-change parameters. Under a Weyl element the position values are permuted
  (`positionValue_of_weyl`), and the multiset is invariant.
- `positionCocharacter_placeConj`: `λ_{w̄, rev k} = -λ_{w,k}`. With `f_{w̄} = f_w` it gives
  `positionValue_placeConj`: `positionValue s ξ w̄ (rev k) = (positionValue s ξ w k)⁻¹`.
  `baseChangeParameter_placeConj`: the parameter at `w̄` consists of the inverses of the
  parameter at `w`. This is the conjugate self-duality `BC(π)_{w̄} ≅ (BC(π)_w)^∨` of base
  change from a unitary group.
- `UnramifiedChart.clozelParameter s ξ w` multiplies each element by
  `s^{f_w (1 - n)} = q_w^{(1-n)/2}`, since `q_w = p^{f_w}` is the residue cardinality of
  `K_w` (Mathlib's inertia degree of the unramified place `w`). It is Clozel's
  `r^T(𝓕_w)` of (5.3), with eigenvalues `q_w^{(1-n)/2} t_{π,w}`, and the unprimed
  `baseChangeParameter` is his `t_{π,w}` of (5.2).
- `UnramifiedChart.IsBaseChangeParameterOf π s w t`, for a smooth representation `π` of
  `G(ℚ_p)` over `L` and `t : Sym Ωˣ n` with `Ω` an extension of `L` and `s` a square root
  of `p` in `Ω`: `t` is the base-change parameter of some principal-series parameter
  `ξ : T →* Ωˣ` of `π` (Kottwitz takes `Ω = L̄`). `IsBaseChangeParameterOf.unique`: if any
  two principal-series parameters of `π` are Weyl equivalent, which is the uniqueness
  half of the Satake parametrization and is not assumed, then the base-change parameter
  of `π` at `w` is unique.
- `complexSqrtPrime p : SqrtPrime p ℂ` is the positive square root of `p`, the choice
  behind the unitary correspondence over `ℂ`.
  `UnramifiedChart.baseChangeEigenvalues ξ w : Langlands.Unramified.Eigenvalues n` is
  the base-change parameter for complex coefficients and this square root. It is
  literally an element of the published `Eigenvalues n = Sym ℂˣ n`, so its Euler
  polynomial `eulerPolynomial` is the denominator of `L(s, BC(π)_w)` at `X = q_w^{-s}`.
- `partialCocharacter E p n w i = Σ_{k < i} λ_{w,k}`. At a split place its point is
  `diag(p^{(i)}, 1^{(n-i)})` in the `GL_n(K_w)` factor.
- `UnramifiedChart.SplitPlaceHeckeNormalization Kp` is the normalization statement, for
  a compact open level `Kp` whose subgroup is the chart's level. Let `π` be a complex
  representation with principal-series parameter `ξ` and let `w` be a split place. Then
  on `K_p`-fixed vectors, the published double-coset operator
  `LevelHecke.heckeOperator` of the point of `partialCocharacter w i` acts by
  `√p^{f_w i (n-i)} · e_i(baseChangeEigenvalues ξ w)`. Here `√p^{f_w} = √q_w`, and
  `e_i` is the published `elementaryCoefficient`. This is exactly the scalar of
  `HasSphericalHeckeSpectrum` for the `GL_n(K_w)` factor. The coset-sum operator of
  `LevelHecke` equals the Haar-normalized operator of `HeckeOperators` for the measure
  giving `K_p` mass one. The statement is a proposition. Its proof, the
  minuscule-coweight Satake computation for the `GL_n(K_w)` factor (Gross 1998 (3.13);
  Kottwitz 1984, Theorem 2.1.3), is a separate obligation, and nothing here assumes it.

## Scope and provenance

This is a derived, concrete presentation of the unramified base change for the groups of
item 1. The source normalization is that of Clozel (5.2) and the published `GL_n` spectra.
Not proved here: the Satake computation behind `SplitPlaceHeckeNormalization`, the global
base-change theorems of Clozel, Harris–Labesse or Harris–Taylor (automorphic statements
owned elsewhere), and existence or uniqueness of principal-series parameters (item 2).
The parameters are defined from principal-series parameters. No structure field stores a
parameter, and no Satake or Langlands correspondence is assumed.

Formal dependencies: `Langlands.Shimura.Unitary.KottwitzPrincipalSeries` (item 2),
`Langlands.Shimura.Unitary.KottwitzChart` (item 1),
`Langlands.Representation.Unramified.HeckeOperators` (`Eigenvalues`,
`elementaryCoefficient`), `Langlands.Shimura.LevelHecke` (`heckeOperator`),
`Langlands.Shimura.Levels` (`CompactOpenLevel`), and Mathlib (`Sym`, `Fin.revPerm`,
`Real.sqrt`). Environment: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
