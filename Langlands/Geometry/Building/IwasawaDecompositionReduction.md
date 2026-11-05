# The chamber Iwasawa decomposition from the relative Tits system

This derived internal unit reduces the chamber Iwasawa decomposition, Kaletha–Prasad
Theorem 5.3.3 (`G(F) = U(F) N(F) P_C` for a chamber `C`), to algebraic statements about the
rational points of the reductive group. It does not prove the exact global target
`IwasawaDecompositionStatement`. The algebraic inputs stay explicit premises, and none of
them is proved here.

## The conditional statement

`IwasawaDecompositionReductionStatement` is the implication from five Library statements to
`IwasawaDecompositionStatement`, all at the same universe `u`:

- `RelativeTitsSystemStatement`: the relative Tits system `(G(F), P_∅(F), N(F), S)` (Borel–Tits
  5.15–5.16);
- `RootRankOneFactorizationStatement`: the rank-one factorization (KP 2.11.17);
- `RelativeRootSystemStatement`;
- `StandardParabolicEndpointsStatement`;
- `RelativeRoot.DynamicRootOrderedProductStatement`.

The conclusion is the unchanged published target: for every nonarchimedean local field `F`,
every affine group scheme `G` over `F` and every `P : ParahoricBuildingData G` satisfying the
apartment axioms, every chamber `C` and every generic cocharacter `ν` give
`P.IwasawaDecomposition C ν`. `iwasawaDecompositionReduction` proves this implication. It
applies `iwasawaDecompositionStatement_of_statements` to the five premises.

## The argument

Write `B = P(ν)(F)` for the rational points of the dynamic parabolic of `ν`, and
`X = B N(F) P_C`.

**Tits systems.** `Langlands.Group.IsTitsSystem.leftStabilizer X` is the subgroup of all `g`
with `g x ∈ X ↔ x ∈ X` for every `x`. `IsTitsSystem.mem_of_stable` then shows the following.
Suppose `X` contains `1` and is stable under left multiplication by `B` and by every
representative of every simple reflection. Then `X` is the whole group. The stabilizer
contains `B` (use `b⁻¹ ∈ B` for the reverse direction). It contains each representative `n` of
a simple reflection `s`, because `n⁻¹` also represents `s = s⁻¹`. It therefore contains every
element of `N`. This follows by induction on `π n ∈ closure S = W`: the identity case uses
`ker π = B ∩ N`, the product case uses the surjectivity of `π`, and the inverse case uses
that the stabilizer is a subgroup. Then
`B ⊔ N = ⊤` makes the stabilizer everything, and `g = g · 1 ∈ X`.

**KP Lemma 5.3.1 at a chamber.** `oppositeFactor_mem_parahoric` and
`oppositeFactors_mem_parahoric` take a nonidentity `u ∈ U_c(F)` with `u ∉ P_C` and a
normalizing product `u' u u'' ∈ N(F)` with `u', u'' ∈ U_{-c}(F)`. They show that
`u', u'' ∈ P_C`. Take the point `x` with `C = F(x)`. On a facet, the root fixers equal the
filtration subgroups (`rootFixer_eq_filtration_of_isFacet`, using axiom AS 4). So `u ∉ P_C`
gives `φ_c(u) < 0` at `x`. Valuation axiom V 5 gives `φ_{-c}(u') = -φ_c(u) > 0`. Hence `u'`
lies in the root fixer of `-c` and so in `P_C`. Applying the same argument to
`u''⁻¹ u⁻¹ u'⁻¹ ∈ N(F)` gives `u''⁻¹ ∈ P_C`, hence `u'' ∈ P_C`.

**One root group.** `rootGroupPoints_le_dynamicParabolic`: if `⟨d, ν⟩ > 0`, then `U_d(F)` lies in
the dynamic unipotent of `ν`, and hence in `B`. `normalizer_mul_rootGroup_mem` shows that
`n u ∈ X` for `n ∈ N(F)` and `u ∈ U_c(F)`, where `c` is a relative root. Let `d = n · c`, which
is again a relative root. Since `ν` is generic, `⟨d, ν⟩ ≠ 0`. There are two cases.

- If `⟨d, ν⟩ > 0`, then `n u = (n u n⁻¹) n` with `n u n⁻¹ ∈ U_d(F) ⊆ B`.
- If `⟨d, ν⟩ < 0`, either `u ∈ P_C`, or the rank-one factorization gives `m = u' u u'' ∈ N(F)`.
  The factors `u', u''` lie in `U_{-c}(F)`, and `-c` is a relative root because `m` represents
  the reflection in `c` (`IsRelativeReflection.neg_mem_relativeRoots`). By the lemma above,
  `u'' ∈ P_C`. Then `n u = (n u'⁻¹ n⁻¹) (n m) u''⁻¹`, where `n u'⁻¹ n⁻¹ ∈ U_{-d}(F)` and
  `⟨-d, ν⟩ > 0`.

**A simple reflection.** `simpleReflection_mul_mem` takes a representative `n₀` of a simple
reflection `s` in the simple root `a`, and `b n p ∈ X`. It shows that `n₀ b n p ∈ X`. It uses
`HasSimpleRootParabolicFactorization` and `P_∅(F) = B` to write `b = b' u` with `u ∈ U_a(F)`
and `n₀ b' n₀⁻¹ ∈ B`. Then
`n₀ b n p = (n₀ b' n₀⁻¹) · (n₀ n)(n⁻¹ u n) · p`. The previous step applies to `n₀ n` and the
root point `n⁻¹ u n ∈ U_{n⁻¹ · a}(F)`.

**`G(F) = B N(F) P_C`.** `exists_dynamicParabolic_normalizer_parahoric` applies
`mem_of_stable` to the Tits system of `HasRelativeTitsSystem`. Its Borel subgroup is
`P_∅(F)`, which is identified with `B` by the hypothesis `hB`.

**The datum-level theorem.** `iwasawaDecomposition_of_relativeTitsSystem` proves
`P.IwasawaDecomposition C ν` for one datum. It assumes the apartment axioms, a chamber, a
generic `ν`, `RelativeRoot.HasRankOneFactorization P.i`, `HasSimpleRootParabolicFactorization`
and `HasRelativeTitsSystem`. The Library gives three identifications for generic `ν`:
`P_∅(F) = B` (`standardParabolic_empty_eq_dynamic_of_generic`), the standard unipotent `U` of
the empty set equals the dynamic unipotent (`standardUnipotent_empty_eq_dynamic`), and
`Z_G(ν) = Z_G(S)` (`genericCentralizer`). For `g = b n p`, let `l` be the dynamic limit of
`b`. Then `b l⁻¹ ∈ U(F)` (`Dynamic.mul_inv_limit_mem_unipotent`), and `l ∈ Z_G(ν)(F) = Z(F)`
(`Dynamic.limit_mem_centralizer`), so `l ∈ N(F)`. Hence `g = (b l⁻¹) (l n) p`.

**Global assembly.** `iwasawaDecompositionStatement_of_statements` instantiates the datum-level
theorem at `P.S`, `P.i`, with the connected reductive and maximal split torus fields of `P`.
The relative Tits system and the rank-one factorization come from their statements. The
simple-root factorization comes from the Library's `hasSimpleRootParabolicFactorization_of_statements`,
applied to `RelativeRootSystemStatement`, `StandardParabolicEndpointsStatement`, the proved
`genericCentralizer` and `DynamicRootOrderedProductStatement`.
`iwasawaDecompositionStatement_of_structuralStatements` replaces the Tits system premise by
`relativeTitsSystemStatement_of_structuralStatements`. It also uses the proved
`genericCentralizer` and `RelativeRoot.rootSubgroupRealization`. Its premises are
`RelativeWeylCoxeterStatement`, `StandardParabolicEndpointsStatement`,
`RationalBruhatStatement`, `RootRankOneFactorizationStatement`, `RelativeRootSystemStatement`,
`RelativeRoot.DynamicRootOrderedProductStatement` and
`RelativeRoot.RootSubgroupVectorStatement`.

## Provenance

The conclusion is KP Theorem 5.3.3 (Kaletha–Prasad, *Bruhat–Tits theory: a new approach*,
§5.3; PDF pp. 220–221). The proof route is internal and differs from KP's. KP derives the
Iwasawa decomposition from the rational Bruhat decomposition and an analysis of the open cell.
This unit instead uses the standard argument that a subset stable under `B` and the simple
reflections of a Tits system is the whole group. Borel–Tits 5.15–5.16 supplies the relative
Tits system, and KP 2.11.17 supplies the rank-one factorization. KP Lemma 5.3.1 is used only at
a chamber, where it follows from valuation axiom V 5 and the constancy of the root filtrations
on a facet. The five premises of `IwasawaDecompositionReductionStatement` are unproved Library
statements that are owned elsewhere. This unit claims only the conditional implication.
