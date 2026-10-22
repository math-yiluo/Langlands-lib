# Langlands' normalization of local constants

Worker 33 wrote this module for task `e534647a`. It covers Tate's comparison
of the Deligne and Langlands conventions for local constants (Tate 1979,
§3.6) and Deligne's absolute-value formula (5.7.2). The main declaration is
`Langlands.LocalFactor.LanglandsNormalizationStatement`. It is a proposition
only. No local-constant system, self-dual measure or dual measure is
constructed or chosen, nothing is proved, and nothing is assumed as an axiom.

## Objects

Everything comes from the published Library:

- `CommonClosure`: a p-adic field `F`, the finite intermediate extensions
  `E : Extension F` in its algebraic closure, their Weil subgroups `W_E`
  (`weilSubgroup F E`), the continuous exact virtual groups `Virtual F E` with
  their integer degree `degree F E`, additive characters `ψ`, Haar measures
  `μ`, the positive rescaling `scaleHaar F E μ c hc` (the measure `c · μ`),
  the canonical topological data `fieldData F E` of each field, and the
  restriction `reciprocityUnits F e E : W_E → E^×` of a supplied reciprocity
  family `e`.
- `NonabelianSystem`: an assignment `ε_E(x, ψ, μ)` on virtual classes, the
  system property `IsSystem F e ε`, the unit `positiveScale c hc` (the
  positive real `c` as a complex unit), and `FourierDualMeasures F E ψ μ μ'`:
  `μ'` is the Fourier dual of `μ` relative to `ψ` for the plus-sign
  transform, that is, the transform for `μ` followed by the transform for `μ'`
  is reflection `f ↦ f(-·)`.
- `CommonClosureSpectral`:
  - `character F E s`, the character `ω_s : w ↦ q_F^(-s · deg w)` of `W_E`, with
    `q_F = baseCardinality F` the residue cardinality of `F` and `deg` the
    degree over `F`;
  - `virtualTwist F E s`, the twist `x ↦ x ⊗ ω_s` of virtual classes;
  - `SelfDualMeasure F E ψ`, the Haar measures `μ` that are self-dual for
    `ψ`: the transform for `μ`, applied twice, is reflection;
  - Langlands' constant `ε_L(x, ψ) = conditionalLanglandsConstant F e ε hε E ψ μ x`,
    defined as `ε_E(x ⊗ ω_(1/2), ψ, μ)` for a self-dual `μ`. This is Tate's
    (3.6.1);
  - Langlands' spectral value `ε_L(s, x, ψ) = conditionalLanglandsValue … x s`,
    defined as `ε_L(x ⊗ ω_(s-1/2), ψ)`. This is Tate's (3.6.4). The published
    theorem `conditionalLanglandsValue_eq` identifies it with Deligne's value
    `ε_E(x ⊗ ω_s, ψ, μ)`.
- `VirtualRepresentation`: the continuous contragredient
  `ExactGrothendieckGroup.continuousDual` (an automorphism of the virtual
  group), the determinant character
  `ExactGrothendieckGroup.determinantCharacter` (a homomorphism `W_E → ℂ^×`
  for every virtual class), and the class `ofRepresentation` of a genuine
  continuous representation.
- `FiniteRepresentation.IsUnitary A`: some complex inner product on the space
  of `A` is preserved by every `A(g)`.
- `ConductorExponent` (the published conductor-exponent statement module):
  the bottom intermediate field `base F` (that is, `F`), whose Weil subgroup is
  the whole local Weil group; the virtual class `baseClass F A hA` of a
  genuine continuous representation of it; the finite-inertia presentations
  `Presentation F A` with their rational Artin conductor
  `P.artinConductor hsurj`, computed when the actual restriction map is
  surjective (`hsurj`); and Tate's `n(ψ) = additiveConductor F ψ`, the
  largest `n` with `ψ(π^(-n) O) = 1`.

## The statement

`LanglandsNormalizationStatement` says that for every prime `p` and every
p-adic field `F`, six clauses hold. In each clause the data include a
reciprocity family `e` and an assignment `ε` with `IsSystem F e ε`. In
clauses 1–5 they also include an intermediate field `E`, an additive
character `ψ` of `E`, and a measure `μ` self-dual for `ψ`. Write `ε_L` for
Langlands' constant at `(E, ψ, μ)`, `V*` for `continuousDual V`, `det V` for
the determinant character, and `ψ_a(y) = ψ(a y)` (`ψ.scale a`), so that
`ψ⁻¹ = ψ_(-1)`. All the clauses live in the namespace
`Langlands.LocalFactor.LanglandsNormalization`.

1. `DeligneFromLanglandsStatement` (Tate (3.6.2)). For every positive real
   `c` and every virtual `V`,
   `ε_E(V, ψ, c · μ) = c^(deg V) · ε_L(V ⊗ ω_(-1/2), ψ)`. Every Haar
   measure is `c · μ` for a unique `c > 0`, and then `c = dx/dx_ψ`.
2. `AdditiveCharacterScalingStatement` (Tate (3.6.6)). Let `a ∈ E^×`, let
   `μ_a` be any measure self-dual for `ψ_a`, and let `w ∈ W_E` satisfy
   `reciprocityUnits F e E w = a`. Then for every virtual `V`,
   `ε_L(V, ψ_a) = det V(w) · ε_L(V, ψ)`, where the left side uses `μ_a`.
3. `DualityStatement` (Tate (3.6.7)). Let `μ'` be any measure self-dual for
   `ψ⁻¹`. Then for every virtual `V`, `ε_L(V, ψ) · ε_L(V*, ψ⁻¹) = 1`, the
   second factor using `μ'`. In addition, for every `s ∈ ℂ`,
   `ε_L(s, V, ψ) · ε_L(1 - s, V*, ψ⁻¹) = 1`.
4. `ContragredientProductStatement` (Tate (3.6.8)). Let `w ∈ W_E` satisfy
   `reciprocityUnits F e E w = -1`. Then for every virtual `V`,
   `ε_L(V, ψ) · ε_L(V*, ψ) = det V(w)`. Both factors use the same `μ`.
5. `UnitaryAbsoluteValueStatement` (Tate (3.6.9)). For every genuine
   continuous unitary representation `A` of `W_E`, `|ε_L(A, ψ)| = 1`.
6. `DeligneAbsoluteValueStatement` (Deligne (5.7.2)), at the base field. Let
   `ψ` be an additive character of `F` and `μ` any Haar measure, and let
   `c > 0` be such that `c · μ` is the Fourier dual of `μ` relative to `ψ`.
   Let `A` be a genuine continuous unitary representation of `W_F`, and let
   `P` be a presentation of `A` with surjectivity `hsurj`. Write
   `a = P.artinConductor hsurj` and `n = n(ψ)`. Then
   `|ε_F(A, ψ, μ)|^2 = c^(-dim A) · q_F^(a + n · dim A)`, a real power of
   `q_F`. Here `c = dx'/dx` in Deligne's notation.

### Design choices

- **Supplied self-dual measures.** Langlands' constant is defined in the
  Library only for a supplied self-dual measure. Each clause therefore
  quantifies over self-dual measures for each additive character involved,
  independently of one another. The self-dual measure of a character is
  unique, and the self-dual measures of `ψ` and `ψ⁻¹` coincide. So clauses 2
  and 3 are Tate's identities at the actual self-dual measures. Existence and
  uniqueness of self-dual measures are stated for p-adic fields in the
  published `Langlands.LocalFactor.Harmonic.Statement`
  (`PadicFourierDualityStatement`). This module does not use that statement.
- **Determinants through reciprocity.** Tate writes `(det V)(a)`, the
  determinant read through the reciprocity map. Clauses 2 and 4 instead
  quantify over Weil elements `w` whose image under the supplied reciprocity
  is `a` (respectively `-1`). This follows the published
  `NonabelianSystem.AdditiveCharacterScalingStatement` and selects no
  inverse of the reciprocity map. The value `det V(w)` does not depend on the
  choice of `w`: `reciprocityUnits` is the supplied isomorphism on the
  abelianization composed with the projection, and `det V`, a character,
  factors through the abelianization.
- **Virtual classes.** Clauses 1–4 hold for every exact virtual class,
  because both sides are multiplicative in `V`. Clauses 5 and 6 are stated for
  genuine representations, because unitarity is a property of a
  representation. Clause 6 also needs an Artin conductor, and the Library
  defines one only through presentations.
- **The base field in clause 6.** Clause 6 is stated at the bottom field of
  the common closure, like the published `ConductorExponentStatement`. There
  the Library's finite-inertia presentations apply directly. Since `F` is
  arbitrary, the clause covers every p-adic field, each with its own common
  closure. Over an intermediate field `E ≠ F` one would need presentations of
  representations of `W_E`. Clause 6 holds at every presentation for which
  the actual restriction map is surjective, and surjectivity is an explicit
  hypothesis.
- **Rational conductor.** The Library's Artin conductor is rational. The
  exponent of `q_F` in clause 6 is therefore a real exponent, `Real.rpow`. The
  power of `c` is an integer power (`zpow`).
- **The spectral form of clause 3.** It is the first identity of clause 3
  applied to `V ⊗ ω_(s - 1/2)`, since the contragredient of
  `V ⊗ ω_(s - 1/2)` is `V* ⊗ ω_(1/2 - s)`. It is stated because Tate's
  (3.6.4) introduces exactly this centered spectral variable.

### Why the clauses hold

This explains the hypotheses only and is not part of the statement. The
`NormalizationRelation` inside `IsSystem` says that `|e(w)|_E = q_F^(-deg w)`.
So `ω_s(w) = |a|^s` whenever `w` has image `a`, and `ω_s` is Tate's
`ω_s = ‖·‖^s` read through reciprocity.

- Clause 1 is the Haar scaling law of `IsSystem` together with
  `ω_(1/2) ω_(-1/2) = 1`.
- Clause 2: the measure self-dual for `ψ_a` is `|a|^(1/2) dx_ψ`. Deligne's
  additive-character law (5.4), `ε(W, ψ_a, dx) = det W(a) |a|^(-dim W) ε(W, ψ, dx)`,
  applied to `W = V ⊗ ω_(1/2)`, gives
  `det W(a) = det V(a) |a|^(dim V / 2)`. The three powers of `|a|`, namely
  `1/2`, `1/2` and `-1` times `dim V`, cancel. This is Tate's remark that the
  dependence on `ψ` is "according to (3.6.6) instead of as in (3.4.4)".
- Clause 3 is Deligne's duality (5.7.1),
  `ε(W, ψ, dx) ε(W* ω_1, ψ⁻¹, dx') = 1`, applied to `W = V ⊗ ω_(1/2)` and
  `dx = dx' = dx_ψ`, since `W* ω_1 = V* ⊗ ω_(1/2)`. That law is the published
  `NonabelianSystem.DualFunctionalEquationStatement`.
- Clause 4 follows from clauses 2 and 3: by clause 2,
  `ε_L(V*, ψ⁻¹) = det V(-1)^(-1) ε_L(V*, ψ)`. This is how Tate derives
  (3.6.8).
- Clause 6 is Deligne's derivation of (5.7.2) from (5.7.1). For unitary `V`
  the complex conjugate of `ε(V, ψ, dx)` is `ε(V̄, ψ̄, dx) = ε(V*, ψ⁻¹, dx)`.
  The conductor law (3.4.5) turns `ε(V*, ψ⁻¹, dx)` into
  `q^(a(V) + n(ψ) dim V) ε(V* ω_1, ψ⁻¹, dx)`. Haar scaling and (5.7.1) give
  `ε(V* ω_1, ψ⁻¹, dx) = c^(-dim V) / ε(V, ψ, dx)`.
- Clause 5 follows from clause 6 at `c = 1` and (3.4.5) with `s = 1/2`:
  `|ε_L(V, ψ)|^2 = q^(a + n dim V) · q^(-(a + n dim V)) = 1`. At an
  intermediate field the same computation runs over `E`. This is Deligne's
  remark in §5.6 that Langlands' constants are normalized to have absolute
  value 1.
- Sanity check of clause 6 with `V` trivial, `n(ψ) = 0` and `dx = t dx_0`,
  where `dx_0(O) = 1`. Then `dx' = t^(-1) dx_0`, so `c = t^(-2)`, and
  `ε(1, ψ, dx) = t` (Deligne (5.9)). Hence `|ε|^2 = t^2 = c^(-1)`.

### Related items stated elsewhere or not restated

- Tate (3.6.1) and (3.6.4) are the definitions of
  `conditionalLanglandsConstant` and `conditionalLanglandsValue` in
  `CommonClosureSpectral`.
- The sentence after (3.6.2), the explicit ratio `dx/dx_ψ`, is stated, with
  its sign corrected, in the published `Langlands.LocalFactor.Harmonic.Statement`.
- Tate (3.6.3), the rank-one formula for `ε_L(χ, ψ)`, is a rank-one
  computation. By the rank-one law of `IsSystem`, `ε_L(χ, ψ)` is the abelian
  epsilon expression at `χ ω_(1/2)` and `dx_ψ`. The published
  `PadicAbelianStatement` states Tate's rank-one formulas (3.2.6) and the
  absolute value 1 of the centered abelian constant for unitary `χ` and the
  self-dual volume. The quotient form (3.6.3) is not restated here.
- Tate (3.6.5) is Tate (3.4.5) for `ε_L`. Since `ε_L(s, V, ψ)` is Deligne's
  value at a self-dual measure, it is the published
  `ConductorExponent.SpectralConductorStatement` at a self-dual measure.
- Tate (3.6.10) and (3.6.11), on the constant `ε_1` with `dx_1(O) = 1` and
  its compatibility with automorphisms of `ℂ`, are not stated here.

## Sources

- `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`:
  J. Tate, *Number theoretic background*, Corvallis Part II (1979). PDF page =
  printed page + 9. §3.6, printed p.17 (PDF p.26): (3.6.1)
  `ε_L(V, ψ) = ε_D(V ω_(1/2), ψ, dx_ψ)` with `dx_ψ` self-dual; (3.6.2)
  `ε_D(V, ψ, dx) = (dx/dx_ψ)^(dim V) ε_L(V ω_(-1/2), ψ)`; (3.6.4)
  `ε_L(s, V, ψ) = ε_L(V ω_(s-1/2), ψ) = ε_D(V ω_s, ψ, dx_ψ)`; (3.6.6)
  `ε_L(V, ψ_a) = (det V)(a) ε_L(V, ψ)`; (3.6.7)
  `ε_L(V, ψ) ε_L(V*, ψ⁻¹) = 1`; (3.6.8)
  `ε_L(V, ψ) ε_L(V*, ψ) = (det V)(-1)`; (3.6.9) `|ε_L(V, ψ)| = 1` if `V` is
  unitary. Printed p.18 (PDF p.27): (3.6.10) and (3.6.11).
- `deligne-1973-local-constants`, SHA-256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`:
  P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*,
  LNM 349 (1973). Printed p.549 (PDF p.49): the remark at the end of §5.6
  that Langlands takes `dx` self-dual for `ψ` and normalizes the constants to
  have complex absolute value 1, and (5.7.1) with `dx'` the Haar measure dual
  to `dx` relative to `ψ`. Printed p.550 (PDF p.50): (5.7.2), for `K`
  non-archimedean and `V` unitary, so that `V* = V̄`,
  `|ε(V, ψ, dx)|^2 = (dx'/dx)^(-dim V) q^(a(V) + dim(V) n(ψ))`. The formula
  page was checked visually. (5.9), printed p.550: the unramified rank-one
  value used in the sanity check.
