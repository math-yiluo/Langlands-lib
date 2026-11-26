# Finite span of intertwining operators: reduction to automorphy and finiteness

Module `Langlands.Global.AdelicIntertwiningFiniteSpanReduction` proves

```
theorem Langlands.Global.intertwiningFiniteSpan_of_uniformAutomorphy
    (hauto : IntertwiningUniformAutomorphyStatement.{u})
    (hHC : ParabolicHarishChandraFinitenessStatement.{u}) :
    IntertwiningFiniteSpanStatement.{u}
```

`IntertwiningFiniteSpanStatement` (module `Langlands.Global.AdelicIntertwiningContinuationReduction`)
is the Lemma of Bernstein–Lapid §8.2: for `φ ∈ 𝒜_P` there are finitely many automorphic forms
`ψ i` on `V(𝔸)M'(F) \ G(𝔸)` and a real `R₀` such that `M(w, λ)φ` lies in the span of the `ψ i`
for every `R₀`-regular `λ`. The two premises are:

- `IntertwiningUniformAutomorphyStatement` (module
  `Langlands.Global.AdelicIntertwiningAutomorphyStatement`): there are `R₁` and an ideal `J` of
  finite codimension of the center `𝔷` such that for every `R₁`-regular `λ` the function
  `M(w, λ)φ` is automorphic on `V(𝔸)M'(F) \ G(𝔸)` and `J` annihilates its infinite slices;
- `ParabolicHarishChandraFinitenessStatement` (module
  `Langlands.Automorphic.GroupSchemeHarishChandraFinitenessStatement`): Harish-Chandra's
  finiteness theorem on `V(𝔸)M'(F) \ G(𝔸)`, for a fixed level `L`, a fixed ideal `J` and a fixed
  finite-dimensional space `E` of functions on `K_∞` containing every `k ↦ f(g k)`.

The module proves neither premise.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`,
§8.2, Lemma and proof, p. 222 (TeX `1911.02342.tex` lines 3274–3290). The proof fixes an
idempotent `ξ` with `δ(ξ)φ = φ`, observes `δ(ξ)M(w, λ)φ = M(w, λ)φ`, produces a
finite-codimensional ideal of `𝔷` annihilating every `M(w, λ)φ`, and concludes by
Harish-Chandra's finiteness theorem. The proof below follows this route; the uniform ideal is
the premise `IntertwiningUniformAutomorphyStatement`.

## The proof

Write `T λ = hK.intertwiningOperator hK' iU l iV c π' w φ λ` and `K_∞ = K.comap (ofInfinite F G)`.

1. **Thresholds.** The premise `IntertwiningUniformAutomorphyStatement` gives `R₁` and `J`. The
   Library theorem `intertwiningIntegrability` gives `R₂` such that the intertwining integrand
   is integrable at every point of `G(𝔸)` for `R₂`-regular `λ`. Put `R₀ = max R₁ R₂`;
   regularity at `R₀` implies regularity at `R₁` and at `R₂`.
2. **Level.** The smoothness of `φ` gives an open subgroup `L₀` of `G(𝔸_f)` fixing `φ`. Let
   `L = L₀ ∩ (K ∩ G(𝔸_f))`. The finite part `K.comap (ofFinite F G)` is open because it
   contains the finite projection of `K`, which is open by the Library's
   `IsMaximalCompactSubgroup.isOpen_finite`; the containment uses the product decomposition
   `IsMaximalCompactSubgroup.eq_comap_prod`. Hence `L` is open. By
   `IsIwasawaCompact.intertwiningOperator_fixedByFiniteLevel`, every `T λ` is right invariant
   under `L`, since the heights are right `K`-invariant.
3. **Types under `K_∞`.** Let `W` be the span of the right translates of `φ` by `K_∞`. It is
   finite-dimensional because `φ` is `K_∞`-finite. Fix the basis `b = Module.finBasis ℂ W` and
   let `c_i(k)` be the `i`-th coordinate of the translate of `φ` by `k ∈ K_∞`
   (`orbitCoordinates`). Let `E` be the span of the finitely many functions `c_i`; it depends
   on `φ` and `K` only. For `R₂`-regular `λ`, the Library's
   `IsIwasawaCompact.intertwiningCompactMap` is a `K_∞`-equivariant linear map `T_λ` from `W` to
   the functions on `G(𝔸)` with `T_λ(φ) = T λ`. Then
   `T λ (g k) = T_λ(k · φ)(g) = ∑ i, c_i(k) T_λ(b i)(g)`, so `k ↦ T λ (g k)` lies in `E` for every
   `g` (`intertwiningOperator_slice_mem_span`).
4. **Finiteness.** Let `S` be the set of the functions `T λ` with `λ` `R₀`-regular. By steps 1–3
   every element of `S` satisfies the four conditions of `ParabolicHarishChandraFinitenessStatement`
   for `J`, `L` and `E`, so the span of `S` lies in a finite-dimensional space and is itself
   finite-dimensional.
5. **Choice of the `ψ i`.** By `Submodule.fg_span_iff_fg_span_finset_subset` there is a finite
   subset `s ⊆ S` with the same span as `S`. The `ψ i` enumerate `s` through `s.equivFin`. Each
   `ψ i` is some `T λ` with `λ` `R₀`-regular, hence automorphic on `V(𝔸)M'(F) \ G(𝔸)`. Every
   `T λ` with `λ` `R₀`-regular lies in `S`, hence in the span of `s`, which is the span of the
   range of `ψ`.

The proof uses the `K_∞`-types of `φ` only through `E` and the level only through `L`. These
are the same for all `λ`, which is the uniformity in Bernstein–Lapid's choice of `ξ`.
