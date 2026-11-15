# Galois descent of root filtration jumps through semilinear root coordinates

Authors: Worker 47.

## Purpose and provenance

This module is internal to the proof of
`Langlands.Geometry.Building.UnramifiedZeroJumpDescentStatement` (Task 6754). That statement is
an internal pointwise formulation of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Proposition 9.4.28(2), in the setting of KP 9.4.27. It says that a jump at `0` of a
root of `G_K`, `K = F^ur`, restricting to `α` gives a jump at `0` of `α` for the restricted
root functions. KP derive 9.4.28 from 9.4.23 (reductive quotients of special fibers of
parahoric group schemes). This module follows a different route, Galois descent at a finite
unramified level, and works at every real value `r`, not only `0`.

1. A jump `u ∈ U_{α_K}(K)` at `r` is defined over a finite Galois subextension `E` of `K/F`,
   i.e. fixed by the kernel of `res : Aut(K/F) → Gal(E/F)`.
2. Norm and trace arguments over `Gal(E/F)` with coefficients in the ring of integers `𝒪_E`
   (`Langlands.GroupScheme.FilteredTraceDescent`) replace `u` by an `Aut(K/F)`-fixed jump.
3. A fixed point of `U_{α_K}(K)` is the extension of a point of `U_α(F)`
   (`exists_mem_rootGroupPoints_of_fixed_of_isGalois`), which is a jump of `α` for
   `fieldRestrict ψ`.

Step 2 needs semilinear coordinates on the root groups. These are supplied by the hypothesis
`RootGroupLinearization iS α v` (module `Langlands.Geometry.Building.RootGroupLinearization`).

## Notation

Fix fields `k ⊆ K`, `b = algebraBaseMap k K`, an affine `k`-group scheme `G`
(`[IsAffineHom G.X.hom]`), a commutative `k`-group scheme `S` with `iS : S.toGrp ⟶ G`, and
`α : characterLattice S`. Write `G_K`, `S_K`, `j_K iS` for the base changes along `b` and
`α_K = characterLattice.baseChange b S α`. Let `ψ : RootFunctionFamily S_K G_K`, and write

- `U = rootGroupPoints (j_K iS) α_K` and `U₂ = doubleRootGroupPoints (j_K iS) α_K`;
- `σ · g = rationalConjugate k K G σ g` for `σ ∈ Aut(K/k)`;
- `M_r = {g ∣ g ∈ U ∧ r < ψ α_K g} * U₂` (as a set).

The jump predicate is `IsRootFiltrationJump i φ a r`: the filtration `rootFiltration i φ a r`
is not contained in `{g ∣ g ∈ U_a ∧ r < φ a g} * U_{2a}`. `fieldRestrict ψ α g` is
`ψ α_K (rationalExtend k K G g)`.

The three hypotheses on `ψ` used throughout are:

- `hmin` (ultrametric on `U`): `min (ψ α_K g) (ψ α_K h) ≤ ψ α_K (g * h⁻¹)` for `g, h ∈ U`;
- `hgal` (Galois invariance): `ψ α_K (σ · g) = ψ α_K g` for `g ∈ U`;
- `htor` (torus invariance): `ψ α_K (T_t g T_t⁻¹) = ψ α_K g` for `g ∈ U` and
  `t ∈ characterValuationKernel v S_K` (the points of `S_K` at which every character has
  valuation one), where `T_t = rationalPoints.map (j_K iS) t`.

## Generic results (any `K/k`)

| Declaration | Content |
|---|---|
| `rootFunction_le_one_of_min_le` | Under `hmin`, `ψ α_K g ≤ ψ α_K 1` for `g ∈ U` (take `h = g`). |
| `isRootFiltrationJump_fieldRestrict_of_not_lt` | Under `hmin`, if `α_K` has a jump at `r` for `ψ` and `¬ r < ψ α_K 1`, then `α` has a jump at `r` for `fieldRestrict ψ`. |
| `rationalExtend_mem_doubleRootGroupPoints` | For a split torus `S` and `[LocallyOfFiniteType G.X.hom]`: `rationalExtend k K G` maps `U_{2α}(k)` into `U₂`. |
| `isRootFiltrationJump_fieldRestrict_of_fixed` | For `[IsGalois k K]`, `[Smooth G.X.hom]`, a split torus `S` and a root `α`: an element `h ∈ U` with `r ≤ ψ α_K h`, `σ · h = h` for all `σ`, and `h ∉ M_r` gives a jump of `α` at `r` for `fieldRestrict ψ`. |
| `exists_fixed_jump_of_rootGroupLinearization` | The finite-level descent step, described below. |

Proofs.

- `isRootFiltrationJump_fieldRestrict_of_not_lt`: let `u` be a witness of the jump of `α_K`.
  Then `r ≤ ψ α_K u ≤ ψ α_K 1`, so `1` lies in the filtration of `α` at `r`. If the filtration
  were contained in the set of the jump predicate, there would be `y ∈ U_α(k)` with
  `r < ψ α_K (rationalExtend y) ≤ ψ α_K 1`. This contradicts `¬ r < ψ α_K 1`.
- `rationalExtend_mem_doubleRootGroupPoints`: by cases on whether `2α` is a relative root. If
  it is, then so is `2α_K` (`mem_roots_baseChange_iff`), and `rationalExtend_mem_rootGroupPoints`
  applies to `2α`. Otherwise `U_{2α}(k)` is trivial.
- `isRootFiltrationJump_fieldRestrict_of_fixed`: `h = rationalExtend h₀` with
  `h₀ ∈ U_α(k)` by `exists_mem_rootGroupPoints_of_fixed_of_isGalois` (a root is nonzero). Then
  `h₀` lies in the filtration of `α` at `r`. If `h₀ = y w` with `y` in the strict part and
  `w ∈ U_{2α}(k)`, then `h = rationalExtend y · rationalExtend w ∈ M_r`, a contradiction.

### The finite-level descent step

`exists_fixed_jump_of_rootGroupLinearization iS α v hlin ψ hmin hgal htor res s hs ρ incl hincl
hunit hdual htrace r hr1 u huU hur hufix hu`. Hypotheses beyond `hmin`, `hgal`, `htor`:

- `v : Valuation K Γ₀` and `hlin : RootGroupLinearization iS α v`;
- a finite group `Γ` with `res : Aut(K/k) →* Γ` and a section `s` (`hs : res (s γ) = γ`);
- commutative rings `R`, `R₀` with `[Algebra R₀ R]`, an action `ρ : Γ →* (R ≃ₐ[R₀] R)` and
  `incl : R →+* K` with `incl (ρ (res σ) x) = σ (incl x)` (`hincl`);
- `hunit`: `v (incl x) = 1` for every unit `x` of `R`;
- `hdual`, `htrace`: every `Γ`-stable subring of `R` containing all squares of units contains a
  dual family `a j, c j` with `∑ j, a j * ρ γ (c j) = if γ = 1 then 1 else 0`, resp. an element
  `θ` with `∑ γ, ρ γ θ = 1`;
- `r < ψ α_K 1` (`hr1`), and `u ∈ U` with `r ≤ ψ α_K u`, fixed by `σ` whenever `res σ = 1`,
  and `u ∉ M_r`.

Conclusion: there is `h ∈ U` with `r ≤ ψ α_K h`, `σ · h = h` for every `σ ∈ Aut(K/k)`, and
`h ∉ M_r`.

Proof. Destructure `hlin` into `n, m, d, q, e` and its conditions. Let `act` be
`σ ↦ rationalConjugate k K G σ` as a homomorphism `Aut(K/k) →* MulAut G_K(K)`. Elements of
the kernel of `res` fix `incl x` by `hincl`. For a unit `x` of `R`, `c = incl x` is a unit of
`K` with `v c = 1` (by `hunit`) that is fixed by the kernel of `res`. Condition 9 of
`RootGroupLinearization` applied to `c ^ 2` (if `d = 1`) or to `c` (if `d = 2`) gives a torus
point `T_t`, fixed by the kernel of `res`, with `q (T_t g T_t⁻¹) = incl (x ^ 2) • q g` on `U`.
By `htor` it preserves `ψ α_K` on `U`. Applied to `c`, condition 9 gives a torus point with
`e (T_t g T_t⁻¹) = incl (x ^ 2) • e g` on `U₂`. This point preserves `U₂` because `q` vanishes
exactly on `U₂`. These are the hypotheses `hsq_q`, `hsq_e` of
`FilteredTraceDescent.exists_fixed_not_mem_mul_of_subring` (with `Λ = WithTop ℝ`,
`H = G_K(K)`, `L = K`), which gives the result. The remaining hypotheses of that theorem are
the conditions of `hlin` and `hmin`, `hgal`, rewritten through `act σ = rationalConjugate k K
G σ`. The theorem is applied a few arguments at a time (`have k1 := …`, then `k2 … k5`):
elaborating the whole application at once exceeds the heartbeat limit.

## The maximal unramified extension

Namespace `MaximalUnramified`. Here `F` is a nonarchimedean local field, `K = F^ur =
inertiaFixedField F`, and `valuation F` is the normalized valuation of `K`. The local
normed-field, ultrametric and completeness instances reuse `localNormedField`,
`localNormedField_ultrametric` and `localNormedField_complete`, with module-specific
names so this module can be imported together with `UnramifiedOmegaGaloisStable`.

| Declaration | Content |
|---|---|
| `valuation_inclusion_integers_le_one` | For a finite subextension `E ≤ K` of `F^sep/F` and `x` in the ring of integers `LocalUnramified.integers F E`: `valuation F (inclusion x) ≤ 1`. |
| `valuation_inclusion_integers_eq_one` | For a unit `x` of `LocalUnramified.integers F E`: `valuation F (inclusion x) = 1`. |
| `exists_finiteLevel_fixing` | For `[IsAffineHom G.X.hom]`, `[LocallyOfFiniteType G.X.hom]` and `u ∈ G_K(K)`, there is a finite Galois subextension `E ≤ K` such that every `σ ∈ Aut(K/F)` that fixes `E` pointwise fixes `u`. |
| `isRootFiltrationJump_fieldRestrict_of_linearization` | The main theorem, below. |

Proofs.

- `valuation_inclusion_integers_le_one`: an integer of `E` is an integer of `F^sep`
  (`integerInclusion`), which is membership in `fixedFieldIntegers F`, i.e. valuation at most
  one (`mem_valuationSubring_iff`).
- `valuation_inclusion_integers_eq_one`: if `x y = 1` in the integers, the valuations of `x`
  and `y` are at most one with product one, so both are one.
- `exists_finiteLevel_fixing`: `GaloisPoint.exists_finiteUnramified_definition` writes
  `u` (transported by `baseChangeCoeffEquiv`) as the image of a point `x_E` over a finite Galois
  `E ≤ K`. Then `σ · u` is the image of `x_E` under `σ ∘ inclusion = inclusion`, by
  `baseChangeCoeffEquiv_rationalConjugate` and functoriality of `Lie.affineMap`.

### Main theorem

`isRootFiltrationJump_fieldRestrict_of_linearization F iS hS hα hlin ψ hmin hgal htor r hjump`.
Let `G` be an `F`-group scheme with `[IsAffineHom G.X.hom]` and `[Smooth G.X.hom]`, `iS` a
split torus (`hS`), and `α ∈ relativeRoots iS`. Let
`hlin : RootGroupLinearization iS α (valuation F)`, and let `ψ` be a family of root functions
of `(G_K, S_K)` satisfying `hmin`, `hgal` and `htor` for `v = valuation F`. If `α_K` has a jump
at `r` for `ψ` (`hjump`), then `α` has a jump at `r` for `fieldRestrict ψ`.

Proof. If `¬ r < ψ α_K 1`, apply `isRootFiltrationJump_fieldRestrict_of_not_lt`. Otherwise
take a witness `u` of the jump of `α_K`, so `u ∈ U`, `r ≤ ψ α_K u` and `u ∉ M_r`. Choose `E` by
`exists_finiteLevel_fixing`, and make `K` an `E`-algebra through the inclusion. Then

- `Γ = Gal(E/F)`, `res = AlgEquiv.restrictNormalHom E` and `s γ = γ.liftNormal K`, with
  `res (s γ) = γ` by `AlgEquiv.restrict_liftNormal`;
- `R = LocalUnramified.integers F E` with `ρ = LocalUnramified.galoisAction F E` and
  `incl` the inclusion `𝒪_E → E → K`; `hincl` is `AlgEquiv.restrictNormal_commutes`;
- if `res σ = 1`, then `σ` fixes `E` pointwise (`restrictNormal_commutes`), so `σ · u = u`;
- `hunit` is `valuation_inclusion_integers_eq_one`;
- `hdual` and `htrace` are `LocalUnramified.exists_dual_family_of_sq_mem` and
  `LocalUnramified.exists_trace_eq_one_of_sq_mem` (module `GaloisStableSubringTrace`).

`exists_fixed_jump_of_rootGroupLinearization` gives an `Aut(K/F)`-fixed `h ∈ U` with
`r ≤ ψ α_K h` and `h ∉ M_r`. Since `K/F` is Galois (`inertiaFixedField_isGalois`),
`isRootFiltrationJump_fieldRestrict_of_fixed` concludes.

## Implementation notes

- The local instance `zeroJumpGaloisDescent_isAffineHom_baseChange` supplies `IsAffineHom`
  for `(GroupScheme.baseChange (algebraBaseMap k K)).obj G`, by unfolding to `pullback.snd`.
- In the main theorem the generic step is applied with `(k := F) (K := inertiaFixedField F)`,
  a few arguments at a time. Unifying the type of `hmin` with the instantiated generic
  hypothesis is slow but finite. (The instance terms differ in form: for example, the
  `Algebra F K` instance elaborated inside `algebraBaseMap F K` and the synthesized one are
  different terms, though definitionally equal.) The main theorem therefore carries
  `set_option maxHeartbeats 1000000`.
- The names `incl` and `gm` are used because `ι` and `γ` are reserved tokens in the imported
  environment.
