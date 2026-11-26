# The actual source gamma is constant on the parabolics of one semistandard Levi

This module proves the gamma half of Remark (3) of I.1 in J.-L.
Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), printed pp.240–241
(PDF pp.6–7), registered as `waldspurger-2003-plancherel`. The remark
says that `γ(P)` depends only on the Levi subgroup `M` of `P`. Here
`P = P(ζ)` and `P' = P(ζ')` are the dynamic parabolics of two
cocharacters `ζ, ζ'` of a fixed maximal split torus. "Same Levi" is
stated through the relative roots: `⟨α, ζ⟩ = 0` exactly when
`⟨α, ζ'⟩ = 0`, for every relative root `α`.

Waldspurger computes `γ(P)` on one small subgroup adapted to all
semistandard parabolics at once and uses root-subgroup products. The
Lean proof instead moves from `ζ` toward `ζ'` in finitely many steps.
Each step crosses the first point of the real segment from `ζ` to `ζ'`
at which some relative root changes sign. That point is
`(q ζ + p ζ') / (q + p)` for positive integers `q, p`, and the proof uses
its integral multiple `φ = q ζ + p ζ'`, which has the same root signs.
It replaces `ζ` by an integral cocharacter `ζ₁` representing a point of
the segment just past the crossing. When several ratios tie, the
crossing point lies on several root hyperplanes, and the step changes
all the tied signs together. Each step uses the theorem
`gamma_eq_of_wall` of `RationalSourceGammaWall` for `ζ`, `ζ₁` and `φ`. The
number of relative roots on which the two cocharacters have opposite
signs strictly decreases at each step. This route is derived.

## Combinatorics of the walls

The namespace `SourceGammaCommonLevi` contains two statements about
integer-valued functions. For a root `α`, `a = ⟨α, ζ⟩` and
`a' = ⟨α, ζ'⟩`.

- `exists_first_wall`: let `a, a'` vanish at the same points of a
  finite set `R`, and let `a a' < 0` somewhere. Then there are positive
  integers `q, p` such that `f = q a + p a'` vanishes at a point `x₀`
  with `a(x₀) a'(x₀) < 0`. Moreover `f ≥ 0` wherever `a > 0`, and
  `f ≤ 0` wherever `a < 0`. Here `x₀` minimizes the ratio `|a| / |a'|`
  over the points where the signs differ, and `p = |a(x₀)|`,
  `q = |a'(x₀)|`. On the real segment `(1 - t) ζ + t ζ'`, the pairing
  `(1 - t) a + t a'` at a root with opposite signs vanishes when
  `t / (1 - t) = |a| / |a'|`. So the first sign change is at
  `t = p / (q + p)`, the point `(q ζ + p ζ') / (q + p)`. The integral
  cocharacter `φ = q ζ + p ζ'` is `q + p` times that point and has
  pairing `f`. If the minimal ratio is attained at roots with different
  hyperplanes, `f` vanishes at all of them.
- `wall_signs`: let `R` strictly exceed `|a|` and `|a'|`, and let
  `g = R f + a'` be the pairing with `ζ₁ = R φ + ζ'`. Divided by
  `R (q + p) + 1`, the cocharacter `ζ₁` is the point of the segment from
  `(q ζ + p ζ') / (q + p)` to `ζ'` at parameter `1 / (R (q + p) + 1)`,
  just past the crossing. The lemma lists the sign relations between
  `a`, `a'`, `f` and `g` used below. Where `f ≠ 0`, `g` has the sign of
  `f`, because `|R f| ≥ R > |a'|`; where `f = 0`, `g = a'`. For
  example, `f > 0` forces `a > 0` and `g > 0`; `f = 0` forces `g = a'`
  and opposite signs of `a` and `a'` when they are nonzero; and
  `g a' < 0` forces `a a' < 0`. The proof is a case analysis on the sign
  of `f`.

## The theorem

`RationalDynamicSource.gamma_eq_of_pairing_zero_iff` assumes:

- `F` is a nonarchimedean local field, in an arbitrary universe and of
  arbitrary characteristic;
- `G` is connected reductive over `F`, with affine structure morphism,
  locally of finite type;
- `i : S → G` is a maximal split torus;
- `K` is a compact open subgroup of `G(F)`, stable under the dynamic
  limit of `P(ξ)` for every cocharacter `ξ` of `S`;
- `ζ, ζ'` are cocharacters of `S` whose pairings vanish at the same
  relative roots.

It concludes `gamma (groupHom ζ ≫ i) K hK = gamma (groupHom ζ' ≫ i) K hK`,
for the published `RationalDynamicSource.gamma` with its original Haar
normalizations.

## Proof

The proof is a strong induction on the number of relative roots `α` with
`⟨α, ζ⟩ ⟨α, ζ'⟩ < 0`. The relative roots are finite by the published
`IsSplitTorus.finite_relativeRoots`.

*No such root.* Then `ζ` and `ζ'` have the same positive, zero and
nonnegative roots. Two applications of the published
`relativeRootSignInclusions` give `P(ζ) = P(ζ')`. Applied to `-ζ` and
`-ζ'`, and using the published
`groupHom_neg_comp_eq_oppositeCocharacter`, they give
`U(ζ⁻¹) = U(ζ'⁻¹)`. The published `gamma_eq_of_dynamic_subgroups_eq`
concludes.

*Some such root.* `exists_first_wall` gives `q, p` and the integral
cocharacter `φ = q ζ + p ζ'`, which represents the first sign change
`(q ζ + p ζ') / (q + p)` on the segment. Choose an integer `R` strictly
larger than every `|⟨α, ζ⟩|` and `|⟨α, ζ'⟩|`, and put `ζ₁ = R φ + ζ'`,
which represents a point just past the crossing after division by
`R (q + p) + 1`. By `wall_signs`, `ζ₁` has the same
zero roots as `ζ'`. It also has fewer roots of sign opposite to `ζ'`:
every such root already has opposite signs for `ζ` and `ζ'`, and the
root `x₀` on the wall does not. By induction,
`gamma ζ₁ = gamma ζ'`. It remains to check the hypotheses of
`gamma_eq_of_wall` for `χ = ζ`, `χ' = ζ₁` and the wall `φ`.

- `Z(ζ₁) = Z(ζ)` and `Z(ζ) ≤ Z(φ)` follow from the published
  `dynamicCentralizer_le_of_pairing`, because the zero roots match as
  stated.
- The containments `U(φ) ≤ U(ζ) ∩ U(ζ₁)` and
  `U(φ⁻¹) ≤ U(ζ⁻¹) ∩ U(ζ₁⁻¹)` follow from the unipotent half of
  `relativeRootSignInclusions` and the sign relations.
- `U(ζ), U(ζ₁) ≤ P(φ)` and `U(ζ⁻¹), U(ζ₁⁻¹) ≤ P(φ⁻¹)` follow from the
  parabolic half and `Dynamic.unipotent_le_parabolic`.
- `U(ζ) ∩ Z(φ) = U(ζ₁⁻¹) ∩ Z(φ)`: a point of `Z(φ)` centralizes
  `-R φ`, so the published shift lemma
  `Dynamic.mem_unipotent_add_iff_of_mem_centralizer` places it in
  `U(ζ)` exactly when it lies in `U(ζ - R φ)`. The relation
  `0 < a - R f ↔ 0 < -g` of `wall_signs` and the sign criterion give
  `U(ζ - R φ) = U(-ζ₁)`.
- `U(ζ⁻¹) ∩ Z(φ) = U(ζ₁) ∩ Z(φ)` holds in the same way with the shift by
  `R φ`.
- The four limit-stability premises are the hypothesis on `K` for `ζ`,
  `ζ₁`, `φ` and `-φ`.

The local instances have names with the `sourceGammaCommonLevi` prefix.
