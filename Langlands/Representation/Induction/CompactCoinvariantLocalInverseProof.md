# The normalized local-section map into compact-induction coinvariants

Worker 270 proves the published
`Langlands.Induction.CompactCoinvariantLocalInverseExists.{uG,uV}` from
[`CompactCoinvariantLocalInverseStatement`](CompactCoinvariantLocalInverseStatement.md)
as `Langlands.Induction.compactCoinvariantLocalInverseExists`. The proof
follows the elementary route outlined in the statement's Markdown: refine by
compact open subgroups, use common refinements, and conjugate by elements of
`H`. The statement and every imported Lean/Markdown pair are unchanged.

## Exact target

```lean
theorem compactCoinvariantLocalInverseExists :
    CompactCoinvariantLocalInverseExists.{uG, uV}
```

The theorem's type is the published proposition. Its universes `uG` and `uV`
are independent. Exact declaration inspection in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` reports only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.

The final theorem introduces the full telescope and applies the private
`exists_localInverse`. It passes on the compact-open neighbourhood-basis
hypothesis, the smoothness of `σ`, and two consequences of
`hν : QuotientIntegration.IsCompatible H μG μH ν`:

- `hν.right_invariant`: every `QuotientIntegration.rightTranslate H g`
  preserves `ν`;
- `hν.compactOpenQuotientOrbit_mass`: `0 < ν(C_J) < ⊤` for every compact open
  `J`, where `C_J = QuotientIntegration.compactOpenQuotientOrbit H J`.

The published mass theorem derives its bound from the regularity and open
positivity contained in compatibility. Apart from these two consequences, the
neighbourhood basis, and smoothness, the proof uses no hypothesis of the
telescope directly. Every helper declaration is `private`.

## Notation

For a compact open subgroup `K` and a vector `v` fixed by `H ∩ K`, written
`hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup`, write
`s_{K,v} = compactDoubleCosetSection H σ K hK 1 v hv`. Write `ρ` for
`compactInduced H σ` and `[f]` for `Representation.Coinvariants.mk ρ f`. The
private `normalized H σ ν K hK v hv` is the right-hand side of the target:

```text
N(K, v) = (ofReal (ν(C_K)).toReal)⁻¹ • [s_{K,v}].
```

## Orbits and section values

`mem_orbit_iff` shows that `quotientMap H y ∈ C_K` if and only if `y = h * k`
with `h ∈ H` and `k ∈ K`. Hence membership is unchanged by right
multiplication by `k ∈ K` (`mem_orbit_mul_iff`). Left multiplication by
`h ∈ H` does not change the coset `quotientMap H y` (`quotientMap_mul_left`).
`orbit_of_mul_mem` records that if `N ≤ K`, `z ∈ K`, and
`quotientMap H (y * z) ∈ C_N`, then `quotientMap H y ∈ C_K`.

Elements of `CompactFunctions H σ` are equal when their values agree
(`section_ext`). The published `compactDoubleCosetSection_apply` gives
`s_{K,v}(h * k) = σ h v`, and `compactDoubleCosetSection_support_subset`
gives `s_{K,v}(y) = 0` when `quotientMap H y ∉ C_K`
(`section_apply_mul`, `section_apply_of_not_mem`). These two value formulas
give `section_add` and `section_smul`: for a fixed `K`, the section is
additive and complex-homogeneous in `v`. If `N ≤ K`, any `v` fixed by
`H ∩ K` is fixed by `H ∩ N` (`admissible_mono`).

## Refinement by a smaller subgroup

Let `N ≤ K` be compact open subgroups, and let `v` be fixed by `H ∩ K`. The
coset space `Q = K ⧸ N.subgroupOf K` is the private abbreviation
`CosetSpace K N`.
It is finite (`finite_cosetSpace`) by Mathlib's
`Subgroup.quotient_finite_of_isOpen`, since `K` is a compact space and
`N.subgroupOf K` is open in it. The representative `r_q ∈ K` of `q` is the
chosen `q.out` (`cosetRep`). Put

```text
c = #{q ∈ Q : quotientMap H r_q ∈ C_N}     (cosetCount)
a = #Q.
```

*Reindexing (`sum_mul_rep`).* Let `φ : G → M` be a function to an additive
commutative monoid with `φ(y * n) = φ(y)` for `n ∈ N`. Then
`∑_q φ(y * k * r_q) = ∑_q φ(y * r_q)` for `k ∈ K`. The proof uses
`Fintype.sum_equiv` with the permutation `MulAction.toPerm k` of `Q`. By
`QuotientGroup.mk_out_eq_mul`, the representative of `k • q` is
`k * r_q * n` for some `n ∈ N`, and `φ` absorbs `n`.

*Sections (`sum_section_rep`, `sum_translate_section`).* First,
`∑_q s_{N,v}(r_q) = c • v`. If `r_q = p * n` with `p ∈ H` and `n ∈ N`, then
`p = r_q * n⁻¹ ∈ H ∩ K` fixes `v`, so the term is `σ p v = v`. Otherwise the
term is zero. Next, evaluate the sum of right translates
`∑_q ρ(r_q) s_{N,v}` at `y`:

- If `y = h * k` with `h ∈ H` and `k ∈ K`, reindexing applies, because
  `s_{N,v}` is right `N`-invariant (`compactDoubleCosetSection_mul`). The
  published `eval_covariant` then turns the sum into
  `σ h (∑_q s_{N,v}(r_q)) = σ h (c • v) = c • s_{K,v}(y)`.
- Otherwise every term vanishes by `orbit_of_mul_mem`, and so does
  `s_{K,v}(y)`.

Hence `∑_q ρ(r_q) s_{N,v} = c • s_{K,v}`.

*Masses (`indicator_orbit_mul`, `orbit_mass_relation`).* The same pointwise
argument, applied to the right `N`-invariant indicator `1_{C_N}`, gives
`∑_q 1_{C_N}(x · r_q) = c · 1_{C_K}(x)` on `LeftQuotient H`. It is proved on
representatives via `Quotient.inductionOn`. Integrate both sides with
`lintegral_finsetSum` and `lintegral_const_mul`. Because
`rightTranslate H r_q` preserves `ν` (`MeasurePreserving.lintegral_comp`),
each term integrates to `ν(C_N)`. Hence `a · ν(C_N) = c · ν(C_K)` in
`ℝ≥0∞`. Both orbits are open, hence measurable, by the published
`isOpen_compactOpenQuotientOrbit`.

*Comparison (`normalized_refine`).* In the coinvariants,
`[ρ(g) f] = [f]` (`Representation.Coinvariants.mk_self_apply`). Applying
`[·]` to the section identity gives `a • [s_{N,v}] = c • [s_{K,v}]`. Both
masses are positive and finite, so the mass identity passes to real numbers,
and it forces `c ≠ 0`. Field arithmetic in `ℂ` then gives
`N(K, v) = N(N, v)`.

## Choice independence and conjugation

*Common refinement (`normalized_eq`).* Let `K` and `K'` both be admissible for
`v`. Then `K ⊓ K'` is a compact open subgroup: it is the intersection of the
compact `K` with the closed `K'`. It is admissible for `v` by
`admissible_mono`. Two refinements give `N(K, v) = N(K ⊓ K', v) = N(K', v)`.

*Conjugation (`normalized_translate`).* For `h ∈ H`, the private
`conjSubgroup K h` is the open subgroup `h K h⁻¹`. It is compact as the image
of `K` under the continuous conjugation `x ↦ h x h⁻¹`
(`isCompact_conjSubgroup`). The vector `σ h v` is fixed by `H ∩ h K h⁻¹`
(`translate_admissible`). Further,

- `C_{hKh⁻¹} = (rightTranslate H h)⁻¹' C_K` (`orbit_conjSubgroup`);
- `s_{hKh⁻¹, σ h v} = ρ(h) s_{K,v}` (`section_translate`), because
  `p * k' * h = (p * h) * (h⁻¹ * k' * h)` for `k' ∈ hKh⁻¹`, and
  `σ (p * h) v = σ p (σ h v)`.

The class of a right translate is unchanged, and `ν` is invariant under
`rightTranslate H h`. Hence `N(hKh⁻¹, σ h v) = N(K, v)`.

## Construction of the linear map

*Admissible subgroups exist (`exists_admissible`).* Smoothness of `σ` gives
an open subgroup `L` of `H` fixing `v`. In the subspace topology,
`L = H ∩ O` for some open `O ⊆ G` with `1 ∈ O`
(`Topology.IsInducing.subtypeVal.isOpen_iff`). The neighbourhood-basis
hypothesis gives a compact open `K ⊆ O`, so `H ∩ K ⊆ L` fixes `v`.

*The map (`exists_localInverse`).* Choose such a `K_v` for every `v`, and
define `f(v) = N(K_v, v)`.

- *Additivity.* Compare `K_{v+w}`, `K_v`, and `K_w` with the common
  refinement `K_v ⊓ K_w` using `normalized_eq`. Then apply `section_add`
  there.
- *Homogeneity.* `a • v` is admissible for `K_v`. Then `normalized_eq` and
  `section_smul` apply.
- *Invariance.* For `h ∈ H`,
  `f(σ h v) = N(h K_v h⁻¹, σ h v) = N(K_v, v) = f(v)` by `normalized_eq` and
  `normalized_translate`.

`Representation.Coinvariants.lift σ f` therefore defines
`T : Representation.Coinvariants σ →ₗ[ℂ] Representation.Coinvariants ρ` with
`T [v] = f(v)`. For any admissible `(K, hK, v, hv)`, `normalized_eq` gives
`f(v) = N(K_v, v) = N(K, v)`. This is exactly the required
characterization.

## Relation to the literature

The motivating source is cited in the statement's Markdown:
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*,
Ann. Sci. ENS (4) **10** (1977), §5.17, pp.466–467 (registered as
`bernstein-zelevinsky-1977-induced-i`). There, the isomorphism is proved for
the integration map `A`, which goes from the compactly induced space to the
inducing coinvariants. The proof checks regular representations, passes to
free representations, and concludes by exactness through free resolutions.
This proof takes a different route. It builds a map in the other direction
directly from double-coset sections, using only the finite counting arguments
above, right invariance of `ν`, and the positivity and finiteness of orbit
masses. It does not use free resolutions or the integration map.
