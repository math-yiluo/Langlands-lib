# Casselman's criterion for actual rational parabolics

Author: Worker 6. Module `Langlands.Representation.Exponents.ArbitraryParabolicCasselmanStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `ArbitraryParabolicCasselmanCriterionStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.1.2, printed pp.221–224 / PDF pp.227–230. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The theorem refers to IV.3.1–IV.3.2 (printed p.99 / PDF p.105) for square integrability modulo the center, to V.3.14–V.3.15 (printed p.113 / PDF p.119) for the cones, and to V.3.20 (printed pp.115–116 / PDF pp.121–122) for the real part. Its proof ends with V.3.21 (printed p.116 / PDF p.122).

This is a **derived** formulation. It states the condition that the source proof establishes, not the printed one. The difference is explained under "Cone: printed statement and proof" below.

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom`, `hG.smooth` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`. It assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology, as in the published `ArbitraryParabolicExponentStatement`. It then quantifies over

- a measurable structure on `rationalPoints G ⧸ Subgroup.center (rationalPoints G)` that is Borel for the quotient topology, and every Haar measure `haar` on that quotient group;
- every `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)`, with an arbitrary carrier universe `v`.

For such `π`, it assumes `π.IsAdmissible` and `Nonempty (UnitaryCentralCharacter π.representation)`. It then asserts that `IsSquareIntegrableModCenter π.representation haar` holds if and only if the following condition holds. For all

- `p : P ⟶ G`, `l : M ⟶ P`, `r : U ⟶ P`, `a : A.toGrp ⟶ M` with `hp : IsParabolicSubgroup p`, `hl : IsRationalLeviSubgroup l`, `hr : LeviSubgroup.IsGeometricUnipotentRadical r`, `hmul : IsIso (subgroupMultiplication l r)` and `ha : IsSplitComponent a`,
- `pres : ParabolicRootPresentation p l a`,
- `χ : rationalPoints A.toGrp →* ℂˣ` with `IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ`,

we have `Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈ pres.positiveCone`.

## The objects

- `UnitaryCentralCharacter π.representation` is the published datum of a character of the abstract center `Subgroup.center (rationalPoints G)` with open kernel and modulus one, by which the center acts. Its existence is the source hypothesis that `π` "admet un caractère central unitaire".
- `IsSquareIntegrableModCenter` is the published IV.3.2 notion for the abstract center of `G(F)`: admissibility, a unitary central character, and, for every smooth-dual functional `λ` and every vector `v`, the absolute coefficient `|φ_{v,λ}|` descended to `G(F)/Z(G(F))` lies in `L²(haar)`. Every Haar measure on the quotient is quantified; square integrability does not depend on the choice, but the statement does not use that fact. The source proof replaces `Z(G)` by its subgroup `C_{A_G}`, which is cocompact in `Z(G)`, and says the two definitions are equivalent. The statement uses only the IV.3.2 version, which is the one the theorem refers to.
- The parabolic data are those of the published represented-parabolic interface. They range over all actual rational parabolics, rational Levi subgroups, matching geometric unipotent radicals and split components, not only over standard parabolics. The theorem says "pour tout sous-groupe parabolique `P = MN`"; only the proof fixes a minimal parabolic and reduces to standard ones.
- `IsNormalizedJacquetExponent` is the published `χ ∈ Exp(A, r_P^G V)`. It is a smooth character of `A(F)` with a nonzero uniform generalized weight space in the normalized Jacquet module of VII.1.1.
- `pres : ParabolicRootPresentation p l a` is the published verified presentation of the parabolic by a maximal split torus, a generic cocharacter and a set `J` of simple relative roots, compatible with `p`, `l` and `a`. `pres.positiveCone` is the published set of `∑_{β ∈ Δ(P)} c_β β` with all `c_β > 0`. Here `Δ(P)` is `pres.restrictedRoots`, the restrictions to `A` of the simple relative roots outside `J`. This set lies in the full real character space `RealTorusSpace.Vstar A`, which is `𝔞*_M`. It is Renard's `+[𝔞*]^G_P` of V.3.15. When `Δ(P)` is empty, for instance when `P = G`, the cone is `{0}`.
- `normalizedRealPart` is the published real part in the `q^(-s)` normalization (see below).

Every compatible presentation is tested, and none is required to exist. The published temperedness predicate `IsNormalizedExponentTempered` differs here: it also requires `Nonempty (ParabolicRootPresentation p l a)`. The statement is meant unconditionally, for the actual reductive objects it quantifies over. It is not a criterion relative to a structural framework. For a parabolic with no compatible presentation, the right-hand side imposes no condition. So the forward implication needs no existence result. The reverse implication does. The source proof (printed pp.222–224 / PDF pp.228–230) uses the exponents of every standard parabolic containing a fixed minimal parabolic. A proof of the reverse implication must therefore supply compatible presentations for those parabolics, with their Levi subgroups, radicals and split components. For actual parabolics these presentations come from the choices in V.3.14: a minimal parabolic inside `P` and a maximal split torus containing `A_M`. That existence is a proof dependency of the reverse implication. It is not proved in the Library, and this module does not assert it.

## Cone: printed statement and proof

The printed theorem (p.221 / PDF p.227) requires `ℜ(χ) ∈ ^G_P[𝔞*_M]^+`. By V.3.15 this is the coroot chamber `{χ | ⟨χ, β̌⟩ > 0, β ∈ Δ(P)}`, that is, the elements `∑ c_β ϖ_β + μ` with `c_β > 0` and an arbitrary `μ ∈ 𝔞*_G`. The proof establishes a different condition. On p.224 / PDF p.230 it shows that the series converge for all `v, λ` if and only if `|χ(t_{α_i})| < 1` for every normalized exponent `χ` and every `i`. Here the `t_α` form the basis of `S` chosen on p.222 / PDF p.228, with `|α(t_α)|_F < 1` and `|β(t_α)|_F = 1` for `β ≠ α`. The proof then appeals to V.3.21 to "recover the condition of the statement".

In the `q^(-s)` convention, `|χ(t)| = q^(-⟨ℜ(χ), H_M(t)⟩)` with `⟨β, H_M(t)⟩ = v_F(β(t))` (V.3.21). So `|χ(t_{α_i})| < 1` means `⟨ℜ(χ), H_M(t_{α_i})⟩ > 0`. The vectors `H_M(t_{α_i})` pair to zero with all but one element of `Δ(P)` and positively with the remaining one, so their components in `𝔞^G_M` are positive multiples of the fundamental coweights of `Δ(P)`. Under the unitary central character hypothesis, `ℜ(χ)` vanishes on `𝔞_G`, as explained two paragraphs below. The condition therefore says that `ℜ(χ)` is a combination of `Δ(P)` with strictly positive coefficients. This is the root cone `+[𝔞*]^G_P`, the first display of V.3.15, and not the coroot chamber of the printed statement.

The two cones differ in general. For the minimal parabolic of split `SL_3`, `α_1 + 3α_2` lies in the root cone, but `⟨α_1 + 3α_2, α̌_1⟩ = 2 − 3 < 0`, so it is not in the chamber. The Lean statement uses the root cone `pres.positiveCone`. This matches the proof and the closed root cone of the published VII.2.1 temperedness condition (`pres.nonnegCone`). It does not formalize the printed chamber.

The printed chamber also allows an arbitrary `𝔞*_G` component, while the root cone has none. Under the hypothesis of a unitary central character this makes no difference. A normalized exponent restricted to `A_G` is the central character, because `δ_P` is trivial on `A_G`. So its real part vanishes on `𝔞_G`, and its `𝔞*_G` component is zero.

## Real-part convention

`normalizedRealPart hA χ` is the parameter for which a smooth character of `A(F)` has modulus `q^(-⟨ℜ(χ), c⟩)` at `c(ϖ)`, for every cocharacter `c` and the fixed uniformizer `ϖ`. This is the real part obtained by lifting through `s ↦ q^(-s)` in V.3.20. Later in V.3.20 the source also writes the real part as the raw natural logarithm of the modulus. The published API keeps the two apart:

`rawLogRealPart hA χ = (-Real.log (LocalField.residueCardinality k : ℝ)) • normalizedRealPart hA χ`,

and this scalar is negative. The proof above and the positive valuation in V.3.21 use the `q^(-s)` parameter. Passing to the raw-log parameter multiplies by a negative scalar, which maps the root cone onto its negative. When `Δ(P)` is nonempty, these two cones are disjoint, because `Δ(P)` is linearly independent. By V.3.14 (printed p.113 / PDF p.119) it spans `(𝔞^G_M)*`, and its number of elements `|Δ_∅ \ Δ^M_∅|` is the dimension of that space. When `Δ(P)` is empty, both are `{0}`. When the minimal parabolic is proper, only the `q^(-s)` parameter passes the Steinberg check below.

The Steinberg check requires a fixed modulus convention. Write `δ_usual(m) = |det(Ad(m)|_{Lie N})|_F` for the usual modulus. It is the Library's `HaarModulus` character of `u ↦ m u m⁻¹` on the radical image. Renard's `δ_P` is its inverse: V.5.4 (printed p.127 / PDF p.133) gives `δ_P(a) = ∏_{γ ∈ Σ(P)} |γ(a)|_F^{-(m_γ + 2m_{2γ})}`, and the remark on printed p.136 / PDF p.142 says his convention inverts the usual one. The published normalized Jacquet action is `δ_usual^{-1/2} ⊗ V_N`. This is Renard's `δ_P^{1/2} ⊗ V_N` of (VI.1.2.2), so both define the same normalized exponents. For a minimal parabolic, the normalized exponent of the Steinberg representation is `δ_usual^{1/2}`, which is `δ_P^{-1/2}` in Renard's notation. Its `q^(-s)` real part is `ρ = ½ ∑_{γ ∈ Σ(P)} (m_γ + 2m_{2γ}) γ`, which lies in the root cone.

The remaining comparisons need the minimal parabolic to be proper, that is, a nonempty set of relative roots. Then `ρ` is a combination of the simple relative roots `Δ_∅`, a basis of `(𝔞^G_∅)*` (printed p.112 / PDF p.118), with strictly positive coefficients: every positive root is a nonnegative combination of `Δ_∅`, and each simple root occurs in the sum itself. The raw-log real part `-(log q) ρ` has strictly negative coefficients and is not in the root cone. The trivial representation has exponent `δ_usual^{-1/2}` with `q^(-s)` real part `-ρ`, also outside the cone. This matches the fact that the trivial representation is then not square-integrable modulo the center.

When `P = G` is minimal, for instance when `G` is a torus, there are no relative roots, `ρ = 0`, and the root cone is `{0}`. The Steinberg representation is then the trivial representation, and both its `q^(-s)` and raw-log real parts are `0`, which lies in `{0}`. The statement covers this case, and the Steinberg check does not distinguish the two conventions there. The statement uses `normalizedRealPart` and asserts nothing about `rawLogRealPart`.

## Faithfulness notes

- The two source hypotheses on `π` are kept: smooth admissible, with a unitary central character. No irreducibility, finite length or finite-dimensionality is assumed.
- The quotient carries the quotient topology of the canonical topology. Its measurable structure is quantified with `BorelSpace`, and every Haar measure is allowed; their existence is not asserted.
- The local-compactness and nonarchimedean-group instances are standard properties of `G(F)` for a local field. They are quantified, not proved, exactly as in the published exponent statements.

## Provenance

This is a derived statement of VII.1.2 for the represented-parabolic interface. It differs from the printed theorem in two documented ways. The cone is the strictly positive root cone `+[𝔞*]^G_P`, which the source proof establishes, instead of the printed coroot chamber `^G_P[𝔞*_M]^+`. The real part is the explicitly named `q^(-s)` parameter of V.3.20. Its proof remains a separate obligation. So do the existence of compatible presentations for actual parabolics, which the reverse implication depends on, and the comparison of these formulations with the printed ones.
