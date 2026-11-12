# Necessity in Casselman's criterion for represented parabolics

Author: Worker 4712. Module `Langlands.Representation.Exponents.CasselmanNecessity`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

This module states and proves the necessity half of Casselman's
square-integrability criterion, Renard 2026, VII.1.2 (printed pp.221–224 / PDF
pp.227–230), in the formulation of the published
`ArbitraryParabolicCasselmanCriterionStatement`
(`ArbitraryParabolicCasselmanStatement.lean` and its Markdown). Necessity means:
if `π` is square integrable modulo the center, then the normalized real part of
every normalized exponent lies in the positive cone. The proof is unconditional.
It uses no Bruhat–Tits, Cartan-decomposition, Iwahori-contraction or
presentation-existence premise. The converse (sufficiency) is not proved here.

## The statement

`ArbitraryParabolicCasselmanNecessityStatement : Prop` (universes `u` for the
field, `v` for the carrier) quantifies over:

- a nonarchimedean local field `k : Type u` (Hausdorff);
- a connected reductive `G` over `k`, with the published point topology on `G(k)`
  assumed locally compact and nonarchimedean;
- a measurable structure (Borel) on `G(k) ⧸ Z(G(k))` and a Haar measure `haar`
  on it;
- a smooth complex representation `π : SmoothRep.{0, u, v} ℂ G(k)`.

It asserts: if `IsSquareIntegrableModCenter π.representation haar`, then for all
`P M U A`, `p : P ⟶ G`, `l : M ⟶ P`, `r : U ⟶ P`, `a : A.toGrp ⟶ M` with
`IsParabolicSubgroup p`, `IsRationalLeviSubgroup l`,
`LeviSubgroup.IsGeometricUnipotentRadical r`,
`IsIso (subgroupMultiplication l r)`, `IsSplitComponent a`, every
`pres : ParabolicRootPresentation p l a`, and every `χ : A(k) →* ℂˣ` with
`IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ`, we have
`Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈ pres.positiveCone`.

The binders, the predicate on the right and the conclusion are copied verbatim
from the right side of `ArbitraryParabolicCasselmanCriterionStatement`. The
hypotheses `π.IsAdmissible` and `Nonempty (UnitaryCentralCharacter π.representation)`
of that statement are omitted, because the published `IsSquareIntegrableModCenter`
already contains admissibility and a unitary central character. The proposition
therefore implies the left-to-right implication of the criterion for every `π`
covered by it. Renard's theorem is an equivalence: "π est de carré intégrable
modulo le centre si et seulement si, pour tout sous-groupe parabolique `P = MN`
de `G`, et pour tout exposant normalisé `χ` de `π` pour le sous-groupe
parabolique `P = MN`, `ℜ(χ) ∈ ^G_P[𝔞*_M]^+`". This statement is its "only if"
part. The comparison between the strictly positive root cone
`pres.positiveCone` and the printed condition, and the `q^(-s)` normalization of
the real part, are as documented in `ArbitraryParabolicCasselmanStatement.md`.
This statement adopts both without change.

The proof is `arbitraryParabolicCasselmanNecessity :
ArbitraryParabolicCasselmanNecessityStatement.{u, v}`.

## Supporting theorems in this module

- `splitComponentPointsMap_cocharacterPoints`: the image in `G(k)` of the
  split-component point `m(t)`, for `m` a cocharacter of `A`, is
  `cocharPoint (m ≫ a ≫ l ≫ p) t`.
- `norm_lt_one_of_squareIntegrable_dynamic_of_eq`: the dynamic bound
  `norm_lt_one_of_squareIntegrable_dynamic` (`CasselmanDynamicNecessity.md`),
  restated for subgroups `N`, `L` given only up to equality with the dynamic
  radical and Levi.
- `norm_latticeSection_lt_one_of_squareIntegrable` (strict bound on the closed
  chamber). In the setting of the statement, let `m` be a cocharacter of `A`
  with `⟨f ≫ α, m⟩ ≥ 0` for every simple root `α ∉ J` and `> 0` for one of them,
  where `f : A ⟶ T` and `J` come from `pres`. Then
  `‖χ(latticeSection m)‖ < 1`, where `latticeSection m = m(ϖ)`.
- `normalizedRealPart_mem_positiveCone_of_squareIntegrable`: the conclusion of
  the statement for fixed data.

## Proof of the strict bound

Let `ζ` be the standard cocharacter of `T` for `J` given by
`pres.isCompatible.realization`, so `range p = P(ζ)` and `range (l ≫ p) = Z(ζ)`.
Put `ν_m = f_* m` (`cocharacterMapInt`). Its pairings are
`⟨α, ν_m⟩ = ⟨f ≫ α, m⟩` (published `RelativeRoot.latticePairing_restrict_cocharacterMapInt`).

1. Signs. `ν_m` pairs nonnegatively with every positive relative root. The proof
   is by `positiveRelativeRoots_induction`: the selected roots restrict to zero
   on `A` (`selectedRoot_restrict_eq_zero`), and the other simple roots pair
   nonnegatively by hypothesis. A positive root with `⟨α, ζ⟩ = 0` lies in the
   closure of `J` (`pairing_eq_zero_iff_mem_closure`), so it restricts to zero on
   `A` and `⟨α, ν_m⟩ = 0`. By genericity of the presentation's cocharacter and
   `relativeRootNegation`, every relative root with `⟨α, ζ⟩ ≥ 0` has
   `⟨α, ν_m⟩ ≥ 0`. The same holds for `-ζ` and `-ν_m`.
2. Dynamic inclusions. Put `χd = ζ ≫ i` and `ξ = ν_m ≫ i`. The published
   `relativeRootSignInclusions` turns step 1 into `P(χd) ≤ P(ξ)` and
   `P(χd⁻¹) ≤ P(ξ⁻¹)`, using `groupHom_neg_comp_eq_oppositeCocharacter`. Hence
   `U(χd)(k) ⊆ P(ξ)(k)` and `U(χd⁻¹)(k) ⊆ P(ξ⁻¹)(k)`.
3. A root point. For a simple root `α ∉ J` with `⟨f ≫ α, m⟩ > 0`, the published
   `RelativeRoot.exists_rootPoint_actual` gives `x ≠ 1` in the root subgroup
   `U_α(k)`. Since `⟨α, ζ⟩ > 0` (standardness) and `⟨α, ν_m⟩ > 0`,
   `RelativeRoot.subgroup_le_dynamicUnipotent` places `x` in `U(χd)(k)` and in
   `U(ξ)(k)`.
4. Identification. The represented radical and Levi points are the dynamic ones:
   `pointImage (r ≫ p) = U(χd)(k)` by the published `pointImage_radical_eq_dynamic`
   (with `dynamicGeometricUnipotentRadical`), and
   `pointImage (l ≫ p) = Z(χd)(k)` from the realization. The published
   `isNormalizedJacquetExponent_iff` makes `χ` a generalized eigencharacter of
   the normalized Jacquet module, pulled back along
   `splitComponentPointsMap (l ≫ p) a`. That map lands in the center of the
   Levi points (`splitComponentPointsMap_mem_center`).
5. Test points. With `ϖ` the uniformizer unit (`ϖⁿ → 0`), `a0 = m(ϖ)` maps to
   `ξ(ϖ)`. With `mb = pres.standardCocharacterLift hζ` (so `f_* mb = ζ`),
   `b0 = mb(ϖ)` maps to `χd(ϖ)`. Both use
   `splitComponentPointsMap_cocharacterPoints` and the presentation's
   `factor_comp`. The dynamic bound gives `‖χ(a0)‖ < 1`.

## Proof of the cone membership

Apply the published cone criterion `pres.mem_positiveCone_of_latticePair`
(`CasselmanChamberBoundCone.md`; rational independence of the simple roots by
`pres.linearIndependent_simpleRoots`) to `x = normalizedRealPart χ`.

- Central directions. Let `m` be orthogonal to all simple roots outside `J`. Then
  `m ≫ a ≫ l ≫ p` is central (`pres.isCentral_of_pairing_eq_zero`). The published
  `normalizedJacquetExponent_realPart_restrict_eq_zero`, with the unitary central
  character contained in square integrability, gives `latticePair x m = 0`, by
  naturality `pair_cocharacterMapReal`.
- Chamber directions. For `m` as in the strict bound, `‖χ(m(ϖ))‖ < 1`. The
  published `norm_eq_rpow_normalizedRealPart` and `valuation_latticeSection` give
  `‖χ(m(ϖ))‖ = q ^ (-latticePair x m)` with `q > 1` the residue cardinality. So
  `latticePair x m > 0` (`Real.rpow_lt_one_iff_of_pos`).

## Provenance and differences from Renard

The statement is a source-faithful restriction of the published criterion
statement to its necessity direction, as explained above (provenance: source,
Renard VII.1.2, printed p.221 / PDF p.227). The proof follows the structure of
Renard's argument (printed pp.222–224 / PDF pp.228–230): volumes of Iwahori double
cosets, the modulus character, exact coefficients from Jacquet eigenvectors,
divergence of `∑ c |χ(z)|²`, and V.3.21. It differs in four points:

- The Iwahori subgroups come from the dynamic open cell, not from Bruhat–Tits
  theory and the Cartan decomposition.
- The test elements differ. Renard's cone `S` has a basis `t_α`
  (`α ∈ Δ_∅`) with `|α(t_α)| < 1` and `|β(t_α)| = 1` for `β ≠ α` (printed
  p.222 / PDF p.228). For a fixed `P = MN` with two or more simple roots outside
  `M`, an individual `t_α` with `α` outside `M` lies on a chamber wall: another
  simple root `β` outside `M` has `|β(t_α)| = 1`, so `t_α` does not contract the
  root subgroup of `β` and is not strictly contracting on `N`. The elements at
  which Renard evaluates coefficients are the products `z ∈ S'_M(n)`, in which
  every simple root outside `M` has exponent `> n`. For `n` large these lie in
  `A_M^+(ε)`, where the asymptotic formula (VI.9.6.5) applies (printed p.223 /
  PDF p.229). The `t_{α_i}` serve as coordinates on the lattice `S_M ≅ ℤ^d`:
  convergence of `∑_{z ∈ S'_M(n)} c |χ(z)|²` is decided by `|χ(t_{α_i})| < 1`
  for all `i` (printed p.224 / PDF p.230). The Lean proof instead treats each
  closed-chamber cocharacter `m` with one positive pairing separately. It uses
  the sequence `m(ϖ)ⁿ ζ(ϖ)`, `n ∈ ℕ`, where `m(ϖ)` is only a weak contraction (it
  may lie on a chamber wall) and `ζ(ϖ)` is a strict contraction. On this
  sequence the coefficient of a joint Jacquet eigenvector is an exact geometric
  sequence in `n`, with no asymptotic formula (`JointIwahoriEigenCoefficient.md`,
  `IwahoriSquareIntegrableBound.md`, `CasselmanDynamicNecessity.md`).
- The represented parabolic `P` need not be standard: the presentation supplies
  its own torus, generic cocharacter and standard cocharacter `ζ`.
- The quotient is `G(k) ⧸ Z(G(k))`.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`;
PDF page = printed page + 6).
