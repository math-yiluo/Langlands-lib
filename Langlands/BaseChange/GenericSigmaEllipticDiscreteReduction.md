# Generic σ-elliptic representations are σ-discrete: a reduction

The module `Langlands.BaseChange.GenericSigmaEllipticDiscreteReduction` proves that
`GenericSigmaEllipticDiscreteStatement` follows from the local integrability of twisted
characters and from two statements on σ-stable inductions. It follows the proof of
Henniart–Lemaire 2011, II.5.8, Lemme (printed p. 106), and of Arthur–Clozel 1989, Chapter 1,
Lemma 2.11 (printed pp. 18–19), without the twisted Weyl integration formula: the Library's
comparison of integrals of concordant functions takes its place, as in the module
`Langlands.BaseChange.SigmaDiscreteEllipticNonvanishingReduction`.

## Statement

`GenericSigmaEllipticDiscreteReductionStatement.{u, v, uW}` is the implication

`TwistedCharacterLocalIntegrabilityStatement.{u, v, uW} →
SigmaInducedEllipticVanishingStatement.{u, v, uW} →
GenericSigmaNoninducedTemperedStatement.{u, v, uW} →
GenericSigmaEllipticDiscreteStatement.{u, v, uW}`

with the same universe parameters for the field `F`, the cyclic `F`-algebra `E` and the
representation space `W` in the premises and in the conclusion. The four propositions are in
the Library, all in the namespace `Langlands.BaseChange` and each in the module of its name:

- `TwistedCharacterLocalIntegrabilityStatement`: for a nonarchimedean local field `F` of
  characteristic zero, a commutative ring `E` that is a cyclic `F`-algebra of group `⟨σ⟩` of
  order `l` (`IsCyclicAlgebra σ l`; so `E` is a finite reduced commutative `F`-algebra, not
  necessarily a field) with its module topology, an irreducible admissible representation `τ`
  of `GL_n(E)` and an isomorphism `A` of `τ` onto `τ^σ`, the twisted character
  `φ ↦ tr(τ(φ) ∘ A)` is represented by a function `Θ`, locally integrable for every Haar
  measure and locally constant near every σ-regular element (Clozel 1987, Theorem 1;
  Arthur–Clozel 1989, Chapter 1, Proposition 2.2). The reduction uses only its specialization
  to a field `E`, the setting of the other three statements.
- `SigmaInducedEllipticVanishingStatement`: for a field `E` that is a cyclic `F`-algebra of
  group `⟨σ⟩` of order `l` with its module topology, if `τ` is irreducible,
  admissible and isomorphic to the smooth induction, from the standard upper block parabolic of
  a block shape with at least two blocks, of a smooth σ-stable representation of the Levi
  product on a space in the universe of `W`, then `tr(τ(φ) ∘ A) = 0` for every `A`, every Haar
  measure and every Schwartz–Bruhat function `φ` supported in the σ-elliptic set
  (Henniart–Lemaire II.4.5).
- `GenericSigmaNoninducedTemperedStatement`: a generic admissible σ-stable representation of
  `GL_{r+1}(E)` with unitary central character that is not isomorphic to any such induction is
  tempered (the classification step of Henniart–Lemaire II.5.8 and Arthur–Clozel Lemma 2.11).
- `GenericSigmaEllipticDiscreteStatement`: the conclusion; a generic admissible representation
  `τ` of `GL_{r+1}(E)` with unitary central character, an isomorphism `A : τ ≅ τ^σ`, a Haar
  measure `μ` and a Schwartz–Bruhat function `φ₀` whose σ-orbital integrals vanish off the
  σ-elliptic set with `tr(τ(φ₀) ∘ A) ≠ 0` make `τ` a σ-discrete series
  (`IsSigmaDiscreteSeries`).

The theorem `genericSigmaEllipticDiscreteReduction` proves the implication.

## Proof of the implication

Fix `F`, `E`, `σ`, `l`, `r`, the Borel σ-algebra on `GL_{r+1}(E)`, and `τ`, `ψ`, `χ`, `A`, `μ`,
`φ₀` as in `GenericSigmaEllipticDiscreteStatement`. `τ` is irreducible (`Whittaker.IsGeneric`
contains it) and admissible, so `TwistedCharacterLocalIntegrabilityStatement`, applied to the
field `E`, gives the twisted character function `Θ` of `(τ, A)`.

1. **Invariance of `Θ`.** For σ-regular `δ` and every `x`, `Θ(x⁻¹ δ x^σ) = Θ(δ)`. The element
   `x⁻¹ δ x^σ` is σ-regular (`IsNormAssociated.twistedConj`, module `Langlands.BaseChange.Norm`).
   `Θ` is locally constant at both points, so `IsTwistedCharacterFunction.hasTwistedCharacterValue`
   (module `Langlands.BaseChange.CharacterFunction`) gives local twisted character values `Θ(δ)`
   and `Θ(x⁻¹ δ x^σ)` there. The value at `δ` is also a value at `x⁻¹ δ x^σ` by
   `HasTwistedCharacterValue.twistedConj` (module
   `Langlands.BaseChange.TwistedCharacter.Saturation`, with the intertwining relation
   `A ∘ τ(g) = τ(g^σ) ∘ A`, `SigmaIntertwiner.comp_apply_eq`). Local values are unique
   (`HasTwistedCharacterValue.unique`).
2. **Vanishing on σ-elliptic test functions forces `tr(τ(φ₀) ∘ A) = 0`.** Suppose
   `tr(τ(φ) ∘ A) = 0` for every Schwartz–Bruhat `φ` supported in the σ-elliptic set. Then `Θ`
   vanishes at every σ-elliptic `δ`: otherwise `δ` is σ-regular, the twisted distribution has
   the local value `Θ(δ) ≠ 0` at `δ`, the σ-elliptic set is open
   (`isOpen_setOf_isSigmaElliptic`, module `Langlands.BaseChange.EllipticLocusClopen`), and
   `exists_support_subset_ne_zero_of_hasLocalValue` (module
   `Langlands.BaseChange.TwistedTraceRegularNonvanishingReduction`) gives a test function
   supported in the σ-elliptic set with nonzero twisted trace. The product `φ₀ Θ` is integrable
   (`Θ` is locally integrable and `φ₀` is continuous with compact support), and
   `∫ φ₀ Θ dμ = tr(τ(φ₀) ∘ A)`. At a σ-regular `δ`, step 1 turns the σ-orbital integrand of
   `φ₀ Θ` into `Θ(δ)` times that of `φ₀`, so the σ-orbital integral of `φ₀ Θ` (for any right Haar
   measure on the σ-centralizer and compatible quotient measure) is `Θ(δ)` times that of `φ₀`.
   If `δ` is σ-elliptic, `Θ(δ) = 0`; otherwise the σ-orbital integral of `φ₀` vanishes by
   hypothesis. By `integral_eq_zero_of_sigmaOrbitalIntegral_eq_zero` (module
   `Langlands.BaseChange.SigmaDiscreteEllipticNonvanishingReduction`),
   `tr(τ(φ₀) ∘ A) = ∫ φ₀ Θ dμ = 0`.
3. **`τ` is not a σ-stable proper induction.** If `τ` were isomorphic to the smooth induction,
   from the standard upper block parabolic of a block shape with at least two blocks, of a
   smooth σ-stable representation of the Levi product on a space in `Type uW`, then
   `SigmaInducedEllipticVanishingStatement` would give the hypothesis of step 2, hence
   `tr(τ(φ₀) ∘ A) = 0`, contrary to the hypothesis on `φ₀`.
4. **Conclusion.** `τ` is σ-stable (by `A`), so step 3 and
   `GenericSigmaNoninducedTemperedStatement` make `τ` tempered. With admissibility,
   irreducibility, σ-stability and step 3, this is `IsSigmaDiscreteSeries σ (r + 1) τ`.

## Sources

- G. Henniart, B. Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011): II.5.8, Lemme and its proof (printed
  p. 106), with II.4.5 (printed pp. 86–88) for the vanishing of twisted characters of σ-stable
  proper inductions on the σ-elliptic set, II.4.7 (printed p. 89) and II.5.15, Proposition 1
  (printed p. 117). The source calls `τ` σ-elliptic when its twisted character function does not
  vanish identically on the σ-elliptic set (II.4.8, Définition, printed p. 91); step 2 derives
  this from the hypothesis on `φ₀` (in the source, by the twisted Weyl integration formula,
  II.2.10, formula (1), printed p. 72). The PDF page is the printed page plus 8.
- J. Arthur, L. Clozel, *Simple algebras, base change, and the advanced theory of the trace
  formula*, Ann. of Math. Stud. 120 (1989): Chapter 1, Lemma 2.11 and its proof (printed
  pp. 18–19), and the proof of Lemma 2.12 (printed p. 19) for the identity
  `tr(Π(φ) I_σ) = ∫ Θ_{Π,σ}(g) φ(g) dg`. The PDF page is the printed page plus 14.
- L. Clozel, *Characters of non-connected, reductive p-adic groups*, Canad. J. Math. 39 (1987),
  149–167, Theorem 1, for the local integrability statement.
