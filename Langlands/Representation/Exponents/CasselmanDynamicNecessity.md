# Square integrability bounds exponents along weak dynamic contractions

Author: Worker 4712. Module
`Langlands.Representation.Exponents.CasselmanDynamicNecessity`. This is a
supporting module for the necessity half of Casselman's criterion (Renard 2026,
VII.1.2). It combines the abstract modules `WeakIwahoriBasis`,
`JointIwahoriEigenCoefficient`, `IwahoriCellVolume`, `IwahoriSquareIntegrableBound`,
`IwahoriModulusIndex` and `ParabolicPointContraction` for the dynamic parabolics of
a connected reductive group. The module adds no definitions.

## Results

`Langlands.Jacquet.exists_common_eigenvector` (linear algebra). Let `f, g` be
commuting endomorphisms of a complex vector space, `Y` a submodule stable under
both, and `v ∈ Y` nonzero with `(f - α)^d v = 0` and `(g - β)^d v = 0`. Then there
is a nonzero `w ∈ Y` with `f w = α w` and `g w = β w`. Proof: take the last nonzero
vector `v₁ = (f - α)^i v` before the first power that vanishes. Then
`(f - α) v₁ = 0`, and `(g - β)^d v₁ = 0` because the operators commute. Take the
last nonzero vector `w = (g - β)^j v₁` in the same way. Then `(g - β) w = 0`, and
`(f - α) w = 0` because `(f - α)` commutes with `(g - β)^j`.

`Langlands.Aubert.General.RationalPointFamily.norm_lt_one_of_squareIntegrable_dynamic`
(main result). Let `k` be a Hausdorff nonarchimedean local field and `G` a
connected reductive group over `k`. Give `G(k)` the published point topology, and
assume it is locally compact and nonarchimedean. Fix a Haar measure on
`G(k) ⧸ Z(G(k))` (Borel). Let `χ, ξ` be cocharacters with

- `U(χ)(k) ⊆ P(ξ)(k)` and `U(χ⁻¹)(k) ⊆ P(ξ⁻¹)(k)` (dynamic radicals and
  parabolics, `χ⁻¹ = Dynamic.inverseCocharacter χ`);
- a rational point `x ≠ 1` in `U(χ)(k) ∩ U(ξ)(k)`.

Let `π` be a smooth complex representation (carrier universe `v`) that is
square integrable modulo the center for this Haar measure
(`IsSquareIntegrableModCenter`, which includes admissibility and a unitary central
character). Let `incl : B →* Z(χ)(k)` be a homomorphism into the center of the
dynamic Levi `Z(χ)(k)`, and let `χB : B →* ℂˣ` be a generalized eigencharacter of
the normalized Jacquet module of `π` along `U(χ)(k)`, pulled back along `incl`.
Suppose `a0, b0 ∈ B` map to `ξ(t)` and `χ(t)` for a unit `t` with `tⁿ → 0`. Then
`‖χB a0‖ < 1`.

## Proof of the main result

Write `N = U(χ)(k)`, `M = Z(χ)(k)`, `O = U(χ⁻¹)(k)`, `b = χ(t)` and `a = ξ(t)`.

1. Basis. Both `b` and `a` lie in `M` and are central there: `b` by the published
   `cocharPoint_mem_centralizer` and `commute_cocharPoint`, and `a` because
   `incl a0` is central. The published inputs give unique factorization in
   `O · M · N` (`dynamic_opposite_factorization_unique`), the open cell
   (`Dynamic.opposite_cell_mem_nhds_one`, transported along
   `rationalPointTopology_eq_rationalSchemeTopology`), and uniform contraction of
   `N` by `bⁿ` and of `O` by `b⁻ⁿ` (`eventually_cocharPoint_pow_conj_mem_ambient`
   for `χ` and `χ⁻¹`). Equicontinuity of conjugation by `aⁱ` on `N` and by `a⁻ⁱ` on
   `O` comes from `exists_nhds_forall_conj_mem_of_parabolic` for `ξ` and `ξ⁻¹`,
   with `S = {0} ∪ {tⁿ}` compact, via `N ⊆ P(ξ)(k)` and `O ⊆ P(ξ⁻¹)(k)`.
   `exists_weakIwahoriBasis_of_contraction` then gives, inside every identity
   neighborhood, a compact open `K` with an Iwahori contraction for `b` and a weak
   one for `a`.
2. Eigenvector. The published `normalizedJacquetOrdinaryEquiv` identifies the
   normalized Jacquet module with the ordinary one twisted by
   `η = closedInverseHalfCharacter`. So `χB` gives a nonzero generalized
   eigenvector `v` of the twisted action. By smoothness, `v` is fixed by an open
   subgroup of `M`. Choose `K` inside a neighborhood inducing that subgroup, so
   `v` is fixed by `K ∩ M`. `exists_common_eigenvector`, applied to the twisted
   actions of `incl a0` and `incl b0` on the `K ∩ M`-fixed vectors (stable by
   the published `characterTwistedAction_mem_fixedVectors_of_mem_center`), gives a
   common eigenvector `w`. Its eigenvalues for the unnormalized action are
   `η(a)⁻¹ χB(a0)` and `η(b)⁻¹ χB(b0)`.
3. Center. `Z(G(k)) ⊆ M`: the published `rationalCenterComparison` identifies
   `Z(G(k))` with the rational points of the scheme center, and
   `center_le_dynamicCentralizer` places that center in `Z(χ)`.
4. Index. `iwahoriIndex K N a > 1`. If the index were `1`, then
   `a (K ∩ N) a⁻¹ = K ∩ N`, so the compact set `C = K ∩ N ∩ U(ξ)(k)` would be
   stable under conjugation by `a⁻ⁿ`. Uniform contraction by `aⁿ` on `U(ξ)(k)`
   shows that every `y ∈ C` equals `1`: otherwise some `aⁿ (a⁻ⁿ y aⁿ) a⁻ⁿ = y`
   would leave the neighborhood `{y}ᶜ` of `1`. But for large `n`, the point
   `aⁿ x a⁻ⁿ` lies in `K` (contraction), in `N` (as `a ∈ M`), and in `U(ξ)(k)`.
   So it equals `1`, and `x = 1`, a contradiction.
5. Bound. `iwahoriIndex_mul_enorm_sq_lt_one` (with the admissibility and
   `L²` parts of `hsq`) gives `[K ∩ N : a(K ∩ N)a⁻¹] · ‖η(a)⁻¹ χB(a0)‖² < 1`, and
   `norm_closedInverseHalfCharacter_sq` gives `‖η(a)‖² = [K ∩ N : a(K ∩ N)a⁻¹]`.
   Hence `‖χB(a0)‖² < 1`.

## Provenance

Derived. This is the necessity argument of Renard VII.1.2 (printed pp.222–224 /
PDF pp.228–230), with three changes:

- The Iwahori-factorizable compact open subgroups come from the dynamic open cell,
  not from the Bruhat–Tits subgroups and the Cartan decomposition V.5.1.
- The test elements are `ξ(t)ⁿ χ(t)`, `n ∈ ℕ`, with `ξ(t)` a weak and `χ(t)` a
  strict contraction. Renard instead sums over the products `z ∈ S'_M(n)` of his
  chamber generators `t_α`, with every exponent of a simple root outside `M`
  larger than `n`, which lie in `A_M^+(ε)` for `n` large. The coefficient is
  exact on the Lean test elements, with no asymptotic expansion.
- The integrals are taken on `G(k) ⧸ Z(G(k))`, not on `G/C_{A_G}`.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`;
PDF page = printed page + 6).
