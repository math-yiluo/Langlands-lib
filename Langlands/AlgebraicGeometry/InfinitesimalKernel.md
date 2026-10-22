# Infinitesimal kernels of group schemes are uniquely divisible

Author: Worker 268.

Module `Langlands.AlgebraicGeometry.InfinitesimalKernel`, namespaces
`Langlands.AlgebraicGeometry.SquareZero` (ring constructions) and
`Langlands.AlgebraicGeometry.InfinitesimalKernel` (points of group objects).
This is a helper module for the proof `Langlands.AbelianScheme.torsionFiniteEtale`.
It uses the test objects `testObj`, `testHom` and charts `Chart` of
`Langlands.AlgebraicGeometry.AffineChartPoints`. It contains no statement
target.

## Main results

Fix a scheme `S`, an affine open `S₀` (`hS₀ : IsAffineOpen S₀`) and a group
object `M : Over S` (`[GrpObj M]`; commutativity is not assumed). Points
`testObj hS₀ D ⟶ M` form a group, by Mathlib's group structure on morphisms
into a group object (`open scoped CategoryTheory.MonObj`). Fix also a
`Γ(S, S₀)`-algebra `D` and an ideal `I` of `D` with `hI : I ^ 2 = ⊥`, a chart
`W : Chart S₀ M`, and

```lean
hW : Set.range (1 : testObj hS₀ (D ⧸ I) ⟶ M).left ⊆ W.U
```

saying that the unit section over `Spec (D ⧸ I)` lands in `W`. Write
`ρ := testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I)` for the closed immersion
`Spec (D ⧸ I) ⟶ Spec D`. The *infinitesimal kernel* consists of the points
`k : testObj hS₀ D ⟶ M` with `ρ ≫ k = 1`. For every natural number `n` with
`hn : IsUnit (n : D)`:

```lean
theorem exists_pow_eq (n : ℕ) (hn : IsUnit (n : D)) (k : testObj hS₀ D ⟶ M)
    (hk : testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫ k = 1) :
    ∃ r : testObj hS₀ D ⟶ M,
      testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫ r = 1 ∧ r ^ n = k

theorem eq_one_of_pow_eq_one (n : ℕ) (hn : IsUnit (n : D)) (r : testObj hS₀ D ⟶ M)
    (hr : testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫ r = 1) (hrn : r ^ n = 1) : r = 1
```

(The variables `hS₀ hI W hW` precede `n` in both theorems.) So every point of
the infinitesimal kernel has an `n`-th root in the kernel, and the kernel has
no nontrivial `n`-torsion.

## Ring constructions (`SquareZero`)

For a commutative `R`-algebra `D` and an ideal `I`:

- `mul_eq_zero`, `sq_eq_zero`: products and squares of elements of `I` vanish
  when `I ^ 2 = ⊥`.
- `pairs R I`, the `R`-subalgebra of `D × D` of pairs `(a, b)` with
  `b - a ∈ I`, and `triples R I`, the subalgebra of `D × D × D` of triples
  `(a, b, b')` with `b - a ∈ I` and `b' - a ∈ I`. They have projections
  `fst`, `snd` and `t₁`, `t₂`, `t₃`, and maps into them built from their entries
  (`pairsLift`, `triplesLift`). Maps into them are determined by their entries
  (`pairs_hom_ext`, `triples_hom_ext`).
- `diag : D →ₐ[R] pairs R I`, `d ↦ (d, d)`.
- `lin R I hI c : pairs R I →ₐ[R] D`, `(a, b) ↦ a + c (b - a)`. It is
  multiplicative because `(b - a)(b' - a') = 0`. Then
  `scale R I hI c : (a, b) ↦ (a, a + c (b - a))` is an endomorphism of
  `pairs R I`.
- `sumSnd`, `(a, b, b') ↦ b + b' - a`, also multiplicative by `I ^ 2 = 0`, and
  `sum R I hI : triples R I →ₐ[R] pairs R I`, `(a, b, b') ↦ (a, b + b' - a)`.
  `pr₁`, `pr₂` are `(a, b, b') ↦ (a, b)` and `(a, b')`. `pair g₁ g₂ h` combines
  two maps into pairs with equal first entries into a map into triples.
- Identities: `scale_zero` (`scale 0 = diag ∘ fst`), `scale_one`,
  `scale_comp_scale` (`scale c ∘ scale c' = scale (c * c')`),
  `sum_comp_pair_scale` (`sum ∘ pair (scale c) (scale c') = scale (c + c')`),
  `sum_comp_pair_id_diag`, `sum_comp_pair_diag_id`, `pr₁_comp_pair`,
  `pr₂_comp_pair`, and `mk_comp_snd` (`snd` and `fst` agree modulo `I`).
- `mk_comp_fst_surjective`, `mk_comp_t₁_surjective`: the maps
  `pairs R I → D ⧸ I` and `triples R I → D ⧸ I` through the first entry are
  surjective. Their kernels consist of nilpotent elements
  (`isNilpotent_ker_mk_comp_fst`, `isNilpotent_ker_mk_comp_t₁`), as does the
  kernel of `D → D ⧸ I` (`isNilpotent_ker_mk`).

## Proof (`InfinitesimalKernel`)

Let `R := Γ(S, S₀)` and `P := pairs R I`.

1. `exists_pt_of_comp_eq_one`: let `q : E →ₐ[R] D ⧸ I` be surjective with
   nilpotent kernel, and let `x : testObj hS₀ E ⟶ M` restrict to `1` along `q`.
   Then `x` has the same image as that restriction (`range_testHom_comp`),
   which lies in `W.U` by `hW`. So `x = W.pt hS₀ ψ` by `Chart.exists_pt`. This
   is applied to `D`, to `P` (via `fst`) and to triples (via `t₁`):
   `exists_pt_pairs`, `exists_pt_triples`.
2. Hence points over `P` that are trivial on `fst` are determined by their
   restriction along `snd` (`pairs_point_ext`). Points over triples that are
   trivial on `t₁` are determined by their restrictions along `pr₁` and `pr₂`
   (`triples_point_ext`). In both cases the points are `W.pt` of algebra maps
   into a subalgebra of a product, and these maps are determined by their
   entries (`Chart.pt_injective`).
3. `sum_comp_eq_mul`: if `x` over triples is trivial on `t₁` with restrictions
   `Q` along `pr₁` and `Q'` along `pr₂`, then its restriction along `sum` is
   `Q * Q'`. By step 2, `x` is the product of the restrictions of `Q` and `Q'`
   along `pair id (diag ∘ fst)` and `pair (diag ∘ fst) id`. The two `sum`
   identities above then give the claim.
4. `scale_add_comp`, `scale_natCast_comp`: for `p` over `P` trivial on `fst`,
   restriction along `scale (c + c')` is the product of the restrictions along
   `scale c` and `scale c'`. Apply step 3 to the restriction of `p` along
   `pair (scale c) (scale c')`. By induction (`scale_zero`, `scale_one`),
   restriction along `scale m` is `p ^ m` for every natural `m`.
5. `exists_pairs_point`: a point `k` of the infinitesimal kernel is the
   restriction along `snd` of a point `p` over `P` trivial on `fst`. Write
   `k = W.pt ψ` and `1 = W.pt ε` by step 1. Then `ψ` and `ε` agree modulo `I`
   by `Chart.pt_injective`, and `p := W.pt (pairsLift ε ψ)`.
6. `exists_pow_eq`: choose `u` with `n * u = 1` and `p` as in step 5. Put
   `r := snd ≫ scale u ≫ p` (as restrictions). Its restriction to
   `Spec (D ⧸ I)` is trivial by `mk_comp_snd`. Moreover
   `r ^ n = snd ≫ scale n ≫ scale u ≫ p = snd ≫ scale (n * u) ≫ p = k`, using
   step 4 and `scale_comp_scale`.
7. `eq_one_of_pow_eq_one`: choose `u` with `u * n = 1` and `p` for `r` as in
   step 5. Then `p ^ n` is trivial on `fst` and on `snd` (because `r ^ n = 1`),
   so `p ^ n = 1` by step 2. Hence `p = scale (u * n) ≫ p = scale u ≫ p ^ n = 1`
   and `r = snd ≫ p = 1`.

The group law of `M` is only used through `MonObj.comp_mul`, `MonObj.comp_one`,
`MonObj.comp_pow` (precomposition is a group homomorphism) and the group axioms
of the hom group.

## Provenance

This is an internal helper. The underlying fact is standard: the kernel of
reduction of a smooth group along a square-zero thickening is a vector group,
hence uniquely divisible by units of the base. That standard argument uses the
tangent space. The implementation instead works directly with points over the
rings of pairs and triples, so it needs no smoothness of `M`, only the
hypothesis `hW`.
