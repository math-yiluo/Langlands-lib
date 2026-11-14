# The normalized inverse Whittaker realization from three inputs

This module reduces the existential conclusion of
`Langlands.Conductor.OrderedUnramifiedWhittakerRealizationStatement` to three
representation-theoretic inputs. It proves no input. All declarations are in
`Langlands.Conductor.OrderedUnramifiedWhittakerReduction`.

## Setting

`F` is any nonarchimedean local field (`Field F`, `ValuativeRel F`, its
`TopologicalSpace`, `IsNonarchimedeanLocalField F`) in any universe. Positive
characteristic is included. The other data are a uniformizer witness `hϖ`, a rank
index `n` (so the group is `GL_(n+1)(F)`), a residue-cardinality witness
`hq : IsResidueCardinality q`, parameters `z : Fin (n + 1) → ℂˣ` and a unitary additive
character `ψ`. Write `ρ = principalSeries hϖ n hq z` for the normalized upper-Borel
unramified principal series from `UnramifiedPrincipalSeries`, `f₀` for its spherical
section `sphericalSection hϖ n hq z`, and `θ⁻¹ = inverseStandardCharacter ψ n` for the
inverse standard character of the upper unipotent group `N`.

No ordering hypothesis on `z` and no conductor hypothesis on `ψ` appears here. These
hypotheses enter only through the inputs.

## Declarations

| Declaration | Content |
| --- | --- |
| `InverseCoinvariants n ψ π` | Abbreviation for the twisted Jacquet module `Jacquet.Localization.Coinvariants π N θ⁻¹` of a representation `π` of `GL_(n+1)(F)`. |
| `exists_functional_of_finrank` | If `finrank ℂ (InverseCoinvariants n ψ ρ) = 1`, there is a nonzero `ℓ ∈ glInverseFunctionals ψ n ρ` such that every element of that space is `c • ℓ` for some `c : ℂ`. |
| `coefficientMap_injective` | Suppose every nonzero subrepresentation `K` of `ρ` has nontrivial `InverseCoinvariants n ψ K.toRepresentation`. Then any `ℓ` whose scalar multiples exhaust `glInverseFunctionals ψ n ρ` has injective `coefficientMap ρ ℓ`. |
| `realization_of_inputs` | The three inputs below imply the existential clause of the target statement for this `F, ϖ, n, q, z, ψ`. |

## The inputs of `realization_of_inputs`

1. `hdim`: `Module.finrank ℂ (InverseCoinvariants n ψ ρ) = 1`. The coinvariants
   are a line.
2. `hnd`: for every `K : Subrepresentation ρ` with `K ≠ ⊥`, the type
   `InverseCoinvariants n ψ K.toRepresentation` is `Nontrivial`. No nonzero
   subrepresentation is degenerate.
3. `hsph`: for every `ℓ ∈ glInverseFunctionals ψ n ρ` and every `g`,
   `(coefficientMap ρ ℓ f₀).val g = ℓ.val f₀ * Spherical.sphericalWhittaker hϖ θ⁻¹ q z g`.

The conclusion is exactly the body of the target statement after its binders:

```lean
∃ ℓ : glInverseFunctionals ψ n (principalSeries hϖ n hq z),
  ℓ.val ≠ 0 ∧
  Function.Injective (coefficientMap (principalSeries hϖ n hq z) ℓ) ∧
  ∀ g, (coefficientMap (principalSeries hϖ n hq z) ℓ (sphericalSection hϖ n hq z)).val g =
    Spherical.sphericalWhittaker hϖ (inverseStandardCharacter ψ n) q z g
```

## Mathematical sources of the inputs

These sources explain where the inputs come from. Nothing here is a Lean dependency.

- `hdim` holds for every `z`. The highest derivative of a product of cuspidal
  representations is one-dimensional (Bernstein–Zelevinsky 1977, Theorem 4.4 and
  Corollary 4.6). For `GL_(n+1)` the highest derivative is the twisted Jacquet module
  for a nondegenerate character of `N`, which is the space `InverseCoinvariants`. The
  characters `χ_i` of `GL_1(F)` are cuspidal.
- `hnd` is where the ordering `|z₁| ≤ … ≤ |z_(n+1)|` is used. Write
  `χ_i = ν^(s_i)` with `ν = |·|` and `q^(-s_i) = z_i`. The condition `χ_j ≇ ν χ_i`
  then reads `z_j ≠ q⁻¹ z_i`. For `i < j` it follows from the ordering, because
  `|q z_j| = q |z_j| > |z_i|`. That condition for `i < j` is the hypothesis of
  Bernstein–Zelevinsky 1977, Theorem 4.11 (p. 456, proof in 4.12–4.15), and the theorem
  says that the product `χ_1 × … × χ_(n+1)` has no nonzero degenerate submodule.
  Identifying this product with `ρ` requires matching the induction conventions.
- `hsph` holds for every `z` when `ψ` has integer conductor. This is the uniqueness of
  spherical Whittaker functions (Shintani). The Casselman–Shalika formula would give
  `ℓ(f₀)` explicitly, but this module does not need it.

## Proofs

**`exists_functional_of_finrank`.** `functionalsLocalizationDualEquiv` identifies
`glInverseFunctionals ψ n ρ` with `Module.Dual ℂ (InverseCoinvariants n ψ ρ)`. A dual
space has the same finite rank (`Subspace.dual_finrank_eq`), so the functional space
has rank one. `finrank_eq_one_iff'` then gives a nonzero spanning element.

**`coefficientMap_injective`.** Let `K` be the kernel of `coefficientMap ρ ℓ`, which is
a subrepresentation because the coefficient map is an intertwining map. Suppose
`K ≠ ⊥`. Then `hnd` gives a nonzero vector in the coinvariants of `K`, and
`Module.Projective.exists_dual_ne_zero` gives a nonzero dual functional on them.
Through `functionalsLocalizationDualEquiv`, that dual functional is a nonzero
`θ⁻¹`-functional `m` on `K`.

The inclusion `K → ρ` is injective, and `ρ` is smooth (`principalSeries_smooth`).
`functionalsComap_surjective_of_smooth` (exactness of twisted coinvariants) therefore
extends `m` to a functional `ℓ'` on `ρ`. Its hypotheses are supplied as follows:

| Hypothesis | Supplied by |
| --- | --- |
| `N` is a union of compact open subgroups | `localField_upperUnipotent_isLimitOfCompactSubgroups` |
| The topology on `N` is nonarchimedean | the local instance `LocalFieldTopology.upperUnipotent_nonarchimedean` |
| `θ⁻¹` is locally constant | `RankinSelberg.isLocallyConstant_of_continuous_complex_character`, applied to the continuity of `inverseStandardCharacter` |

By the spanning hypothesis `ℓ' = c • ℓ`. For `v ∈ K`, evaluating the coefficient
function at `1` gives `ℓ(v) = (coefficientMap ρ ℓ v)(1) = 0`, so `ℓ'` vanishes on `K`.
Hence `m = 0`, a contradiction. So `K = ⊥`, and a linear map with zero kernel is
injective.

**`realization_of_inputs`.** `exists_functional_of_finrank` gives a spanning `ℓ₀`, and
`coefficientMap_injective` makes its coefficient map injective. Suppose
`ℓ₀(f₀) = 0`. Then `hsph` gives `coefficientMap ρ ℓ₀ f₀ = 0 = coefficientMap ρ ℓ₀ 0`.
Injectivity forces `f₀ = 0`, which contradicts `sphericalSection_ne_zero`. So with
`c = ℓ₀(f₀)⁻¹`, the functional `ℓ = c • ℓ₀` has the required properties:

- `ℓ(f₀) = 1`, so `ℓ ≠ 0`.
- Its coefficient functions are `c` times those of `ℓ₀`. Since `c ≠ 0`, its coefficient
  map is injective.
- By `hsph`, `(coefficientMap ρ ℓ f₀)(g) = c · ℓ₀(f₀) · W(g) = W(g)`.
