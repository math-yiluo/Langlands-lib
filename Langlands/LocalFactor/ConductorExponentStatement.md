# Conductor exponents of local constants

Worker 33 wrote this module for task `e534647a`. It covers the
conductor-exponent part of row 9 of the local-factor coverage map. The main
declaration is `Langlands.LocalFactor.ConductorExponentStatement`. It is a
proposition only. No local-constant system, presentation or conductor law is
constructed or chosen, and nothing is assumed as an axiom. The only proved
items are the two helpers `mem_weilSubgroup_base` and `baseInclusion`.

## Objects

Everything comes from the published Library:

- `CommonClosure`: a p-adic field `F`, the finite intermediate extensions
  `E : Extension F` in its algebraic closure, their Weil subgroups `W_E`
  (`weilSubgroup F E`), the continuous exact virtual groups `Virtual F E`,
  additive characters `ψ`, Haar measures `μ`, the canonical topological data
  `fieldData F E` of each field, and the field characters `FieldCharacter F E`
  (continuous homomorphisms `E^× → ℂ^×`). A field character `χ` gives the
  character class `characterClass F e E χ`: the line on which `W_E` acts by
  `χ` composed with the supplied reciprocity component `e`.
- `NonabelianSystem`: an assignment `ε_E(x, ψ, μ)` on virtual classes, with
  the system property `IsSystem F e ε` for a reciprocity family `e`.
- `CommonClosureSpectral`: the value `conditionalDeligneValue x s`
  `= ε_E(x ⊗ ω_s, ψ, μ)` of a virtual class at `s ∈ ℂ`. Here `ω_s` is the
  character `character F E s`, `w ↦ q_F^(-s · deg w)`, and
  `q_F = baseCardinality F` is the residue cardinality of `F`.
- `CommonClosureWeilDeligne`: the inertia subgroup `inertia F E` (the kernel of
  the base degree), the supplied geometric Frobenius elements
  `GeometricFrobenius F E` (elements `Φ` with norm `q_E^(-1)`), the
  Weil–Deligne pairs `Pair F E`, and their full epsilon value
  `conditionalEpsilonValue`. That value is the system value of the underlying
  class times `det(-q_E^(-s) Φ | V^I / (ker N)^I)`, as in Tate (4.1.6).
- `WeilDeligne.conductorCorrection A I`: the dimension of
  `V^I / (ker N)^I`, that is `dim V^I - dim V_N^I` in Tate's notation.
- `Ramification.Padic.FiniteInertiaPresentation F A`, for a representation `A`
  of the actual local Weil group of `F`. It is a finite Galois extension
  `L ⊂ F̄` such that the kernel of the actual restriction map
  `weilInertiaRestriction F L` from Weil inertia to `I(L/F)` acts trivially
  on `A`. Given surjectivity `hsurj` of that map, `P.artinConductor hsurj ∈ ℚ`
  is the Artin conductor of the action descended to `I(L/F)`, computed from
  the ramification filtration of `L/F`.
- `HarmonicAnalysis`: `additiveConductor ψ`, Tate's integer `n(ψ)`, the largest
  `n` with `ψ(π^(-n) O) = 1`.

## Definitions and helpers

All of these live in the namespace `Langlands.LocalFactor.ConductorExponent`.

- `base F` is the bottom intermediate field `⊥`, that is `F` itself, as an
  extension of `F`.
- `mem_weilSubgroup_base` (proved) says that every element of the actual local
  Weil group of `F` lies in `weilSubgroup F (base F)`. The fixing subgroup of
  `⊥` is the whole Galois group (`IntermediateField.fixingSubgroup_bot`).
- `baseInclusion F` (proved continuous) is the resulting continuous
  homomorphism from the local Weil group onto `weilSubgroup F (base F)`. It is
  the identity on underlying elements.
- `baseClass F A hA` is the exact virtual class of a genuine continuous
  representation `A` of `weilSubgroup F (base F)`.
- `Presentation F A` is the type of finite-inertia presentations of `A`
  restricted along `baseInclusion F`. Those are presentations of the same
  action, now viewed on the local Weil group.
- `additiveConductor F ψ` is `n(ψ)` for an additive character of the base.

## The statement

`ConductorExponentStatement` says that for every prime `p` and every p-adic
field `F`, four clauses hold. In each clause the data are a reciprocity family
`e`, an assignment `ε` with `IsSystem F e ε`, an additive character `ψ` and a
Haar measure `μ` of the base, a genuine continuous representation `A` of
`W_F = weilSubgroup F (base F)`, and a presentation `P` of `A` with
surjectivity `hsurj`. Write `a = P.artinConductor hsurj`, `n = n(ψ)`,
`q = q_F`, and `ε(x, s)` for `conditionalDeligneValue F e ε hε (base F) ψ μ x s`.

1. `SpectralConductorStatement`: for every `s ∈ ℂ`,
   `ε(A, s) = ε(A, 0) · q^(-(a + n · dim A) · s)`, with a complex power of
   the positive real `q`.
2. `UnramifiedCharacterStatement`: let `χ` be a field character of `F` that is
   trivial on every unit of valuation one, let `m ∈ ℤ` satisfy
   `m = a + n · dim A` in `ℚ`, and let `c ∈ F^×` have valuation `m`
   (`discreteValuation c = exp(-m)`). Then for every `s`,
   `ε(A ⊗ χ, s) = ε(A, s) · χ(c)`. Here `A ⊗ χ` is the tensor product
   (`continuousTensorSame`) with the character class of `χ`.
3. `UnramifiedTensorStatement`: let `W` be a continuous representation of
   `W_F` that is trivial on `inertia F (base F)`, let `Φ` be a geometric
   Frobenius, and let `m` be as in clause 2. Then for every `s`,
   `ε(A ⊗ W, s) = ε(A, s)^(dim W) · det W(Φ)^m`.
4. `WeilDeligneSpectralConductorStatement`: here `A` is instead a Weil–Deligne
   pair whose underlying representation is continuous, `P` is a presentation
   of that underlying representation, and `Φ` is a geometric Frobenius. Write
   `ε_WD(A, s)` for `conditionalEpsilonValue F e ε hε (base F) ψ μ A hA Φ s`
   and `c_N = conductorCorrection A (inertia F (base F))`. Then for every `s`,
   `ε_WD(A, s) = ε_WD(A, 0) · q^(-(a + c_N + n · dim A) · s)`.

### Design choices

- **The base field only.** The clauses are stated at the bottom field of the
  common closure, where the fixing subgroup is the whole local Weil group.
  There the Library's finite-inertia presentations apply directly through
  `baseInclusion`, with no transport between Weil groups. Since `F` is an
  arbitrary p-adic field, the statement covers every p-adic field, each with
  its own common closure. The same laws over an intermediate field `E ≠ F`
  would need presentations of representations of `W_E`. That requires the
  identification of `weilSubgroup F E` with the local Weil group of `E`
  (task `ef3a09fe`) and is not stated here.
- **Every presentation.** Each clause holds at every presentation of `A` for
  which the actual restriction map is surjective. Surjectivity is an explicit
  hypothesis and is never replaced by an arbitrary map onto a finite group.
  The clauses are not vacuous: the published
  `Langlands.LocalFactor.Ramification.InertiaPresentationStatement` states
  that the restriction is surjective for every finite Galois `L`
  (`WeilInertiaRestrictionSurjectivityStatement`), that every continuous
  action has a presentation
  (`ContinuousWeilFiniteInertiaPresentationStatement`), and that the
  conductor does not depend on the presentation
  (`FiniteInertiaConductorIndependenceStatement`).
- **Rational conductor, integral exponent.** The Library's Artin conductor is
  rational. Clauses 1 and 4 use complex powers of `q`, so no integrality is
  needed. Clauses 2 and 3 quantify over an integer `m` equal to
  `a + n · dim A` in `ℚ`. By Artin's integrality theorem `a` is an integer
  (Tate (3.4.5) calls `q^(a(V))` the absolute norm of the Artin conductor), so
  such an `m` exists. Integrality itself is not asserted here.
- **Normalization of reciprocity.** `IsSystem` contains `NormalizedReciprocity`,
  whose `NormalizationRelation` says that the image of `w` under `e` has
  normalized absolute value `q^(-deg w)`. So `e` sends a geometric Frobenius to
  an element of valuation one, a uniformizer up to a unit. For `W` the
  character class of an unramified `χ`, this gives
  `det W(Φ)^m = χ(e(Φ))^m = χ(c)`, and clauses 2 and 3 agree. Clause 3 is
  stated directly with `Φ`, so it uses no reciprocity map, while clause 2
  keeps Deligne's form with a field character.
- **The spectral twist.** `ω_s(w) = q^(-s · deg w)`, and a geometric
  Frobenius has degree one because its norm is `q^(-1)`. So `ω_s(Φ) = q^(-s)`,
  and `ω_s` is Tate's `ω_s = ||·||^s` read through reciprocity.
- **Residue cardinalities.** Clauses 1 and 4 use `q = baseCardinality F`, the
  residue cardinality from the canonical data of `F`. The Weil–Deligne
  correction and `GeometricFrobenius` use `residueCardinality F (base F)`, the
  residue cardinality from the canonical data of the subfield `⊥`. These are
  different Lean terms for the same number, since `⊥` and `F` are isomorphic
  valued fields. This module does not prove that they are equal.
- **Genuine representations only.** All clauses are stated for genuine
  continuous representations and pairs. The extension of clauses 1–3 to
  virtual `V` follows from additivity of `ε` (Tate (3.4.2), Deligne (5.2)) and
  of the conductor. It is not stated, because the Library has no conductor of
  virtual classes.

### Why the clauses hold

This is recorded only to explain the hypotheses and is not part of the
statement. By Tate (2.3.1) a system satisfying `IsSystem` is determined by its
rank-one values, and Tate derives (3.4.5) and (3.4.6) from the rank-one
formulas by inductivity in degree 0. That gives clauses 1 and 3. In clause 1 the factor
`q^(-a·s) · q^(-n · dim A · s)` is Tate's `f(V)^(-s) δ(ψ)^(-s dim V)` with
`f(V) = q^(a(V))` and `δ(ψ) = q^(n(ψ))`. In clauses 2 and 3 the twist by `ω_s`
commutes with the tensor product, and `a(A ⊗ ω_s) = a(A)` because `ω_s` is
unramified. So the identities at every `s` follow from those at `s = 0`
applied to `A ⊗ ω_s`. Clause 2 is the case `W = χ` of clause 3, as explained
above. For clause 4, the quotient factor satisfies
`det(-q^(-s) Φ | Q) = q^(-s · dim Q) · det(-Φ | Q)` with `Q = V^I / (ker N)^I`.
Multiplying with clause 1 for the underlying representation gives the
exponent `a + c_N + n · dim A`. This is Tate's
`a(V) = a(ρ) + dim V^I - dim V_N^I` together with `ε(V, t) = ε(V) t^(a(V))`,
extended to general `ψ` by (3.4.5).

### Consequences not stated

- Deligne's `ε_0(V) = ε(V) det(-Φ | V^I)` (Deligne (5.1)) and the second
  formulas of (5.5.1) and (5.5.2), with exponent
  `sw(V) + dim V · (n(ψ) + 1)`, follow from the clauses above. The Library has
  no `ε_0`, so they are not stated.
- The Weil–Deligne value does not depend on the Frobenius lift and is
  invariant under equivalence of pairs. Both are already proved in
  `CommonClosureWeilDeligne` (`conditionalEpsilonValue_eq_of_frobenius`,
  `conditionalEpsilonValue_eq_of_equiv`) and are not repeated here.

## Sources

- `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`: J. Tate,
  *Number theoretic background*, Corvallis Part II (1979). PDF page = printed
  page + 9.
  - (3.4.2), (3.4.5), (3.4.6), printed p.15 (PDF p.24): additivity,
    `ε(V ω_s, ψ, dx) = ε(V, ψ, dx) f(V)^(-s) δ(ψ)^(-s dim V)` with
    `δ(ψ) = q_F^(n(ψ))` and `f(V) = q^(a(V))`, and, for `W` unramified,
    `ε(V ⊗ W, ψ, dx) = ε(V, ψ, dx)^(dim W) det W(π^(a(V) + dim V · n(ψ)))`.
  - (4.1.6), printed p.21 (PDF p.30): `a(V) = a(ρ) + dim V^I - dim V_N^I`,
    `ε(V) = ε(ρ) det(-Φ | V^I/V_N^I)` and `ε(V, t) = ε(V) t^(a(V))`, for the
    usual `ψ` and `dx`.
- `deligne-1973-local-constants`, SHA-256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`:
  P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*,
  LNM 349 (1973). §5.1–(5.5.2), printed p.548 (PDF p.48): `ε_0`, additivity
  and, for `χ` unramified,
  `ε(Vχ, ψ, dx) = ε(V, ψ, dx) χ(π^(a(V) + dim V · n(ψ)))` and
  `ε(V, ψ, dx, s) = ε(V, ψ, dx) q^(-(a(V) + dim V · n(ψ)) s)`. (5.5.3),
  printed p.549 (PDF p.49): the same law for an unramified representation `W`.
