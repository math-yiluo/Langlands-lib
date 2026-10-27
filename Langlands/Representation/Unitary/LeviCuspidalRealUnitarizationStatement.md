# Real unitarization of irreducible cuspidal product-Levi representations

`Langlands.LeviCuspidalRealUnitarizationStatement.{uF,uV}` is a closed
proposition definition. It states that every irreducible cuspidal
representation of an actual standard product Levi of `GL_n` becomes
unitarizable after a real power of the block determinant norms. The file
provides no proof. Neither the definition nor the sources cited below prove
the existence theorem.

## Quantifiers and hypotheses

The statement quantifies over every prime `p` (with `Fact p.Prime`), p-adic
field `F : PadicField.{uF} p`, supplied compatible local-field realization
`T : F.TopologicalData`, natural number `n` with `0 < n`, and ordered block
shape `D : GeneralLinear.BlockShape n`. A block shape lists positive block
sizes `D.size i` for `i : Fin D.length` with total `n`. The group
`D.Levi F.Carrier` is the product over `i` of the actual groups
`GeneralLinear (D.size i) F.Carrier`. The proposition installs
`T.topology` on `F.Carrier` with `letI`. The topology on the Levi product is
the one the existing instances derive from it.

It then quantifies over every complex vector space `V : Type uV` and every
actual representation `ρ : Representation ℂ (D.Levi F.Carrier) V`. The field
universe `uF` and the carrier universe `uV` are independent. There are exactly
two hypotheses on `ρ`:

- `Representation.IsIrreducible ρ`, Mathlib's algebraic irreducibility:
  the subrepresentation lattice is a simple order, so `V` is nonzero and has
  no invariant subspaces other than `0` and `V`;
- `CuspidalSupport.IsLeviCuspidal D ρ`, which is
  `IsAdmissible ρ ∧ CuspidalSupport.IsLeviQuasicuspidal D ρ`. Admissibility
  means smoothness, with every vector fixed by an open subgroup, plus finite
  generation of the fixed vectors of every open subgroup. Quasicuspidality
  requires the actual unipotent coinvariants of `ρ` to be subsingleton for
  every standard block refinement `S` of `D` whose refined parabolic
  `refinedParabolic F.Carrier D S` is proper.

The statement has no further hypotheses. In particular it has no unitary or
real central-character hypothesis, scalar-character decomposition,
compactness or square-integrability of coefficients, chosen tensor
presentation of `ρ`, chosen form, prescribed exponent, or support map. No
norm, topology, completion, or finite-dimensionality is put on `V`.

## Conclusion, carrier and sign

The conclusion is

`∃ t : Fin D.length → ℝ, IsUnitarizable (T.leviRealPowerTwist D t ρ)`.

The twist is the published `T.leviRealPowerTwist`. It acts on the **same**
carrier `V` by

`(T.leviRealPowerTwist D t ρ) m v = (∏ i, |det(m i)|_F ^ (t i)) • ρ m v`,

where `|x|_F = q^(-ord x)` is `T.normalizedAbs`, with `q` the residue
cardinality, and the real powers are of positive reals. This interface uses
exponent `+t`. The published cancellation law
`leviRealPowerTwist_neg_cancel` gives
`T.leviRealPowerTwist D (-t) (T.leviRealPowerTwist D t ρ) = ρ`, so `ρ` is the
`-t` twist of the unitarizable representation `ω = T.leviRealPowerTwist D t ρ`.

`IsUnitarizable ω` is `Nonempty (InvariantPositiveForm ω)`. Such a form is an
`InnerProductSpace.Core ℂ V` on the given carrier: a positive definite
Hermitian form, conjugate-linear in the first argument. Every action operator
`ω m` must preserve it. Nothing is said about completeness or about the
topology the form induces. The statement does not say that `t` is unique,
positive, ordered, or has a zero weighted sum. It is not a cone or support
theorem and makes no square-integrability or classification claim.

The statement also does not assert that the twisted representation is again
irreducible or cuspidal. Those transports are owned separately; the existing
`isSmooth_leviRealPowerTwist_iff` only records smoothness.

## Provenance (derived specialization)

This exact product-Levi statement is not stated literally in the sources
below. It is a derived specialization of the following results for a general
p-adic reductive group, applied to `M = ∏ GL_{n_i}(F)`.

- Casselman, *Introduction to the theory of admissible representations of
  p-adic reductive groups*, draft of 1 May 1995 (registered
  `casselman-1995-admissible-representations`, SHA-256
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`). PDF
  page numbers equal the printed ones.
  - §2.1, p.18 defines a unitary representation as one with a `G`-invariant
    anisotropic Hermitian form on `V` itself. Over `ℂ` an anisotropic
    Hermitian form is definite, so up to sign this is the invariant positive
    definite form of `InvariantPositiveForm`. p.21 defines characters, the
    twist `π ⊗ χ` on the same space, and `ω`-representations.
  - §2.5, pp.28–29: Proposition 2.5.4 says an irreducible admissible
    representation that is square-integrable modulo `Z`, with unitary central
    character, is unitary. The proof integrates a coefficient product over
    `G/Z`.
  - §5.1, p.46 defines absolutely cuspidal by `V = V(N)` for every proper
    parabolic `P = MN`, and notes that one parabolic in each conjugacy class
    suffices. For `∏ GL_{n_i}`, every parabolic is conjugate to a standard
    block-upper-triangular one. Together with admissibility, this is our
    `IsLeviCuspidal`.
  - Theorem 5.2.1, pp.46–47: coefficients of absolutely cuspidal
    representations are compactly supported modulo `Z`. Corollary 5.2.3,
    p.47: an irreducible absolutely cuspidal `ω`-representation with unitary
    `ω` is unitary.
  - Lemma 5.2.5, p.48: for a smooth `ω`-representation there is a unique
    positive character `χ` of `G` with `(π ⊗ χ)|_Z` unitary. Its proof
    extends `|ω|` from `Z/Z₀` to a positive character of `T/T₀`, for the
    maximal torus quotient `T`, and takes `χ` to be its inverse. For
    `M = ∏ GL_{n_i}`, that quotient is given by the block determinants. The
    positive characters of `M` factoring through `T/T₀` are exactly
    `m ↦ ∏ |det(m i)|_F^(t i)` with real `t`, which are the characters of
    `T.leviRealPowerCharacter`. With a central character from Schur's lemma,
    and Corollary 5.2.3 applied to `π ⊗ χ`, this is the mathematical route to
    the statement; nothing here proves it. The identification of positive
    characters, and the use of the standard-refinement test in place of all
    parabolics, are our derived
    steps, not text in Casselman.
- Silberger, *Introduction to harmonic analysis on reductive p-adic groups*,
  1979 (registered `silberger-1979-harmonic-analysis`, SHA-256
  `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`; PDF page
  = printed page + 6). Corollary 1.11.8, printed p.68 (read visually): an
  irreducible admissible `π` whose coefficients lie in `L²_r(G, χ)`, for a
  character `χ` of a closed central subgroup, admits an invariant scalar
  product on its space. Corollary 2.8.4, printed pp.114–115 (read visually):
  if a `π`-critical p-pair has a unitary critical exponent, then `π` is
  unitary. These are the same mechanism and are cited only as a cross-check.
- Silberger, *The Langlands quotient theorem for p-adic groups*, Math. Ann.
  236 (1978) (registered
  `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
  SHA-256
  `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`; read
  visually). On p.96 Silberger writes `°ℰ(G)` for the unitary supercuspidal
  classes and defines `χ_ν(m) = q^(√-1⟨ν, H(m)⟩)` for complex `ν`. For real
  `ν₀`, the character `χ_(√-1 ν₀)` is positive real. On p.99, the proof of
  Proposition 5.1 realizes `σ'` as a quotient of `I(P ∩ M', σ_(√-1 ν₀))` with
  `σ ∈ ω ∈ °ℰ(M)`, that is, as a quotient of an induced representation of a
  unitary supercuspidal twisted by a positive real character. This only
  motivates the interface "cuspidal equals unitary cuspidal up to a real
  twist" and is not a proof of it.

No errata for these sources were found in the project or the Library.

## Proof obligations

A proof must establish the existence of `t` and of an actual invariant
positive form on `V` for every `p`, `F`, `T`, `n`, `D`, `V`, `ρ` satisfying
only the two hypotheses. Following the route above, it would at least need:

1. a central character of the irreducible admissible `ρ` on the center of
   the product Levi (Schur's lemma for admissible representations);
2. a real exponent vector `t` such that the twisted central character has
   absolute value one. On the center, the block scalars `z_i I_{n_i}`, the
   twist multiplies by `∏ |z_i|^(n_i t_i)`, so each block gives one scalar
   equation, solvable in real numbers;
3. compactness modulo the center, or at least square-integrability, of the
   coefficients of the twisted representation. This uses quasicuspidality,
   which the twist does not change because the real character is trivial on
   the unipotent radicals of the refinements, together with admissibility;
4. an actual invariant positive form on `V` from these coefficients, as in
   Casselman 2.5.4, either directly on the product Levi or through existing
   `GL` results and an actual product assembly.

Each analytic step and each transport between representations must be
proved, not assumed. A proof must not use the positive-root support statement
this feeds, nor any consumer of this unitarization step.
