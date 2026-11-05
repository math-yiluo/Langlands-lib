# Moderate growth of coefficients on the literal Levi point subgroup

Lean module: `Langlands.Representation.Plancherel.ParabolicLeviModerateGrowth`, namespace
`Langlands.Plancherel`.

## Purpose and provenance

Provenance: internal. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), Corollary I.4.4, printed p. 245 (PDF p. 11), states that the
coefficients of an admissible finite-length representation have moderate growth with one
exponent. The Library states this on the actual point group of a connected reductive group as
`RationalFiniteLengthModerateGrowthStatement` (unproved there in general). The conditional
intertwining statement, however, induces from representations of the literal Levi point
subgroup `Mpt = parabolicLeviPointSubgroup p l ⊆ G(F)`, and measures heights in `G`. This
module transports the statement from `M(F)` to `Mpt` along the published topological
isomorphism `parabolicLeviPointHomeomorph r : M(F) ≃ₜ* Mpt`, measuring heights with a closed
representation `ρ₀` of `G`. It also names the conclusion, `HasCommonCoefficientGrowth`, which
is the coefficient hypothesis used by the cone reduction of the conditional intertwining
statement. Nothing is transcribed from the source.

## Setting and notation

`F` is a nonarchimedean local field; `G`, `P`, `M` are group schemes over `Spec F` with `G`
affine over the base and `M.X.left` affine; `r : ParabolicRootPresentation p l a` presents the
parabolic `p : P ⟶ G` with Levi `l : M ⟶ P`. `G(F)` carries `rationalPointTopology F G.X`. For a
closed representation `ρ₀ : G ⟶ GL_N` (`N > 0`), `rationalMatrixNorm F ρ₀ g` is the height of
`g`, and `ρ₀.restrict (l ≫ p) = (l ≫ p) ≫ ρ₀` is its restriction to `M`.

## Declarations

- `HasCommonCoefficientGrowth π H` (definition, a `Prop`), for a smooth representation `π` of a
  topological group `L` and `H : L → ℝ`: there is `d : ℕ` such that for every vector `v` and
  every smooth functional `ℓ` there is `c > 0` with `‖ℓ (π(m) v)‖ ≤ c * H(m) ^ d` for all `m`.
- `rationalMatrixNorm_restrict_leviComposite`: for `g ∈ M(F)`, the height of `g` for
  `ρ₀.restrict (l ≫ p)` is the height for `ρ₀` of its image `rationalPoints.map (l ≫ p) g`.
- `parabolicLevi_exists_coefficientGrowth` (main theorem): assume
  `RationalFiniteLengthModerateGrowthStatement` and `M` locally of finite type. For every closed
  representation `ρ₀` of `G` on a nonempty `Fin N` and every admissible finite-length smooth
  representation `π` of `Mpt`,
  `HasCommonCoefficientGrowth π (fun m => rationalMatrixNorm F ρ₀ m)`.

## Proofs as implemented

**Restriction.** Unfold the height and apply the public `rationalMatrix_restrict`; the two
sides then agree by definition of `rationalPoints.map`.

**Main theorem.** `M` is connected reductive (field `isConnectedReductive` of the rational Levi
in `r`), and `ρ₀.restrict (l ≫ p)` is closed, as a composite of the closed subgroups `l`, `p`
and `ρ₀` (public `IsClosedSubgroup.comp`). Let `e = parabolicLeviPointHomeomorph r` and
`π' = SmoothRep.pullback e π`, the representation `g ↦ π(e g)` of `M(F)` on the same space. It is
admissible (public `isAdmissible_comp_continuousMulEquiv`) and of finite length (public
`pullbackFunctor_preservesFiniteLength`). The moderate-growth statement for `M`, `ρ₀.restrict
(l ≫ p)` and `π'` gives one exponent `d`. For `v` and `ℓ`, the same linear functional is smooth
for `π'` (public `isSmoothVector_dual_comp_continuousMulEquiv_iff`), so there is `c > 0` with
`‖ℓ (π'(g) v)‖ ≤ c * ‖g‖ ^ d` on `M(F)`. At `g = e⁻¹ m`, `π'(g) v = π(m) v`, and by the
restriction lemma and public `parabolicLeviPointHomeomorph_apply_coe` the height of `g` is the
`ρ₀`-height of `m`.

## Scope

The moderate-growth statement is a hypothesis; the Library proves it only conditionally on
further structural statements. No convergence of intertwining integrals, no cone estimate and
no part of the host theorem is proved here.
