# Characterizations by L-factors of pairs

Author: Worker 11. This module, in namespace `Langlands.RankinSelberg`, states
two representation-side theorems of Henniart, *Une caractérisation de la
correspondance de Langlands locale pour GL(n)*, Bull. SMF 130 (2002):

- Théorème 1.6(b), equivalence of (i) and (ii): supercuspidal
  representations are characterized by the triviality of their L-factors of
  pairs against supercuspidal representations of smaller rank.
- Théorème 1.7(b): a non-supercuspidal irreducible representation is
  determined by the pole orders at `s = 0` of its L-factors of pairs against
  essentially square-integrable representations of smaller rank.

The L-factor of an arbitrary irreducible admissible pair is the relation
`IsLanglandsPairLPolynomial` of the module
`LanglandsQuotientLFactorStatement`, JPSS's definition through the Langlands
classification. The module defines one function and three statements. None
of the statements is proved.

## Source

Henniart 2002, read from the text layer (printed page = 0-based PDF index +
587).

- **§1.1, printed page 588.** `F` is a nonarchimedean local field.
  - `A(n)` is the set of isomorphism classes of smooth irreducible
    representations of `GL_n(F)`.
  - `A_0(n)` is the subset of supercuspidal classes.
- **§1.2, printed pages 588-589.** For smooth irreducible `π` of `GL_n(F)`
  and `π'` of `GL_(n')(F)`, `L(s, π × π')` is the factor defined by
  Jacquet, Piatetski-Shapiro and Shalika [6] (or by Shahidi). The L-factors
  have the form `P(q^(-s))^(-1)` with `P` a complex polynomial of constant
  term 1.
- **Théorème 1.6(b), printed pages 590-591.** Let `n ≥ 2` and `π ∈ A(n)`.
  The following are equivalent:
  - (i) `π ∈ A_0(n)`;
  - (ii) for `r = 1, …, n - 1` and `ρ ∈ A_0(r)`, `L(s, π ⊗ ρ) = 1`. The
    printed `π ⊗ ρ` is the pair `π × ρ`, as everywhere else on these pages;
  - (iii) for the same `r` and `ρ`, `γ(s, π ⊗ ρ, ψ)` is a monomial in
    `q^(-s)`.
- **§1.7, printed page 591.**
  - `A_2(n)` is the set of classes of essentially square-integrable
    representations of `GL_n(F)`.
  - For `π`, `v_r(π)` is the function on `A_2(r)` sending `ρ` to the order
    of the pole at `s = 0` of `L(s, π × ρ)`. The printed text says
    "pour `π ∈ G(n)`", a misprint for `A(n)`, since the function is
    evaluated on representations of `GL`.
  - **Théorème 1.7(b).** Let `n ≥ 2`, `π ∈ A(n) − A_0(n)` and
    `π' ∈ A(n)`. If `v_r(π) = v_r(π')` for `r = 1, …, n - 1`, then
    `π = π'`.
- **§2.8, printed page 596.** The L-factor of a pair is the product of the
  L-factors of the essentially square-integrable data, which is JPSS (9.5) in
  product form.

## Definitions

- `lPolynomialPoleOrderAtZero P` is `P.rootMultiplicity 1`. This derived
  definition is the order of the pole at `s = 0` of `L(s) = 1 / P(q^(-s))`:
  - the map `s ↦ q^(-s)` sends `0` to `1`;
  - its derivative `-log q · q^(-s)` does not vanish, so it is locally
    biholomorphic at `0`;
  - hence the order of vanishing of `P(q^(-s))` at `s = 0` is the
    multiplicity of the root `1` of `P`.

  Mathlib's `rootMultiplicity` is `0` for the zero polynomial; no
  L-polynomial is zero (its constant term is `1`). The identification with
  the analytic pole order is explained here, not proved in Lean.

The statements quantify over:

- every prime `p` and every `F : PadicField p` with its canonical
  topological data;
- every `UnitaryAdditiveCharacter` `ψ` of `F`;
- every `ν` in the published
  `LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`;
- every `n`.

The rank of `π` is `n + 2` (Henniart's `n ≥ 2`), and the test ranks are
`r + 1` with `r ≤ n` (Henniart's `1 ≤ r ≤ n - 1`).

- `SupercuspidalLFactorCharacterizationStatement` (Théorème 1.6(b),
  (i) ⇔ (ii)) applies to every smooth `π` of `GL_(n+2)(F)` (carrier in
  `max uF uV`) that is irreducible (`Representation.IsIrreducible`) and
  admissible (`SmoothRep.IsAdmissible`). It says that
  `GeneralLinear.IsSupercuspidal π.representation` holds if and only if the
  following condition holds. For every `r ≤ n` and every smooth `ρ` of
  `GL_(r+1)(F)` (carrier in `max uF uW`) that is irreducible and satisfies
  `GeneralLinear.IsSupercuspidal`, `IsLanglandsPairLPolynomial F ψ ν π ρ 1`
  holds, that is, `L(s, π × ρ) = 1`.
- `SquareIntegrablePoleOrderCharacterizationStatement` (Théorème 1.7(b))
  applies to irreducible admissible smooth `π`, `π'` of `GL_(n+2)(F)` with
  `π` not supercuspidal. Its hypothesis concerns every `r ≤ n` and every
  smooth `ρ` of `GL_(r+1)(F)` that is irreducible and essentially
  square-integrable (`IsEssentiallySquareIntegrable` of the canonical
  topological data). For each such `ρ` there must be polynomials `P` and `P'`
  with these properties:
  - `IsLanglandsPairLPolynomial F ψ ν π ρ P`;
  - `IsLanglandsPairLPolynomial F ψ ν π' ρ P'`;
  - `lPolynomialPoleOrderAtZero P = lPolynomialPoleOrderAtZero P'`.

  Under these hypotheses the statement concludes
  `Nonempty (π.representation.Equiv π'.representation)`.
- `PairLFactorCharacterizationStatement` is the conjunction of the two
  statements.

## Interpretation

- **Classes and representatives.** Henniart works with isomorphism classes;
  the statements quantify over actual representations.
  - The published `GeneralLinear.IsSupercuspidal` (admissibility and
    vanishing of all proper Jacquet modules) is invariant under equivalence
    (`isSupercuspidal_iff_of_equiv`).
  - So is the L relation (`IsPadicSymmetricLPolynomial.congr_equiv`).
  - Equality of classes is `Nonempty` of a representation equivalence.
- **Universes.** The test representations `ρ` range over carriers in the
  fixed universe `max uF uW`, independent of the universe of `π`. An
  irreducible smooth representation of `GL_r(F)` has countable dimension:
  it is spanned by the translates of one vector fixed by an open subgroup
  `K`, indexed by the countable set `GL_r(F)/K`. Hence every class in
  `A_0(r)` or `A_2(r)` has a representative in every universe, and
  quantifying over one universe is quantifying over all classes. This
  derived argument is not proved in the Library.
- **The L-factors.**
  - Henniart's `L(s, π × ρ)` for arbitrary irreducible pairs is that of
    JPSS. JPSS define it for nongeneric pairs through the Langlands
    classification ((9.4)). Henniart §2.8 gives it as the product over
    essentially square-integrable data.
  - Both descriptions are stated in the module
    `LanglandsQuotientLFactorStatement`; the relation used here is
    `IsLanglandsPairLPolynomial`.
  - In 1.6(b) "`L = 1`" is the relation with polynomial `1`.
  - In 1.7(b) the hypothesis asks for the L-polynomials of both pairs to
    exist. Their existence for irreducible admissible pairs is
    `LanglandsPairLFactorExistenceStatement`, and they are unique
    (`IsLanglandsPairLPolynomial.unique`). Hence, given existence, the
    hypothesis is exactly `v_r(π) = v_r(π')`.
- **Genericity.** No representation is assumed generic. The tests are
  irreducible supercuspidal or essentially square-integrable
  representations, which are generic, and `π`, `π'` are arbitrary
  irreducible admissible representations, as in the source.
- **Omitted part of 1.6(b).** Condition (iii), on `γ(s, π × ρ, ψ)`, is not
  stated. For nongeneric `π` the factor `γ` is Henniart's product extension
  (§2.8), which is not defined in the Library.
- **The Galois side.** Théorèmes 1.6(a) and 1.7(a), on representations of the
  Weil–Deligne group, belong to the arithmetic side and are not stated here.
- **Measures and field.** As in the other units, `ν` is self-dual for `ψ`,
  and the L relation does not otherwise depend on `ψ`. `F` is a p-adic field
  (`PadicField`) because the canonical topological data and Langlands data
  are published only for p-adic fields. Henniart's `F` is any nonarchimedean
  local field.

## Lean checks

`lean_check` of the module with declaration
`Langlands.RankinSelberg.PairLFactorCharacterizationStatement`:

- 0 errors and 0 warnings.
- The declaration is a definition returning `Prop`, with universe parameters
  `uF`, `uV`, `uW`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
