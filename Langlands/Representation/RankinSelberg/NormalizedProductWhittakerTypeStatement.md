# Full Whittaker type of normalized upper block induction

Author: Worker 350.

`Langlands.RankinSelberg.NormalizedProductWhittakerTypeStatement.{uF,uW}`
is a proposition definition stating preservation of full Whittaker type under
the existing normalized upper block induction. This module supplies the
interface only; it does not prove that proposition or assume it as an axiom.

## Exact scope

For every prime `p`, every `F : PadicField.{uF} p`, and every nontrivial
continuous unitary additive character `ψ` for
`F.canonicalTopologicalData.topology`, take natural numbers `t`, `k`, an
ordered family `m : Fin k → ℕ`, and
`h : ∑ i, (m i + 1) = t + 1`. The block representations `σ i` act on arbitrary
dependent complex module carriers `W i : Type uW`, for the actual groups
`GL_(m i + 1)(F)`. The sole mathematical premise is that each `σ i` satisfies
`IsOfWhittakerType (m i) (standardCharacter ψ (m i))`.

The conclusion is
`IsOfWhittakerType t (standardCharacter ψ t)
  (F.canonicalNormalizedProductInduced (succBlockShape m h) σ)`.
The canonical topology is installed locally in the character type, each
block premise, and the conclusion, as in `GammaMultiplicativityStatement`.
The field, character, ordered shape and dependent block-family quantifiers
are precisely those of that parent, with its test representation and Haar
measure omitted. The field and block-carrier universes remain independent;
the actual induced function carrier has universe `max uF uW`.
All ranks are positive, including rank one. The equality `h` rules out an
empty family at positive total rank.

For any representation `ρ` of `GL_(n + 1)(F)`, the existing predicate
`IsOfWhittakerType n θ ρ` means:

- `IsAdmissible ρ`;
- `Module.Finite (MonoidAlgebra ℂ (GL_(n + 1)(F))) ρ.asModule`;
- `Nonempty ((Whittaker.functionals (upperUnipotent (n + 1) F) θ ρ) ≃ₗ[ℂ] ℂ)`.

Thus the conclusion asserts finite generation over the actual group algebra
and a linear equivalence of the entire functional space with the scalars.
It does not restrict uniqueness to chosen functionals or a chosen subspace.
The representations may be reducible and infinite-dimensional. Neither
irreducibility nor a genericity hypothesis replaces full Whittaker type;
no property of the induced representation or desired comparison equivalence
is supplied as an extra premise.

## Original source and correspondence

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464; registered source `jpss-1983-rankin-selberg`.
Retained original:
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
SHA256: `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

The following original pages were read visually (one-based PDF page equals
printed page minus 365):

- §0.3, printed pp.375–377 (PDF pp.10–12): upper and lower standard
  parabolics, normalized induction with left covariance and right translation,
  tensor-product inducing action, and the standard character of the upper
  unipotent group. In particular, p.377 displays (9), (10), and (11) give
  the induction conventions.
- §2.1, printed p.385 (PDF p.20), displays (1) and (2): admissible
  finite-type representations whose full space of equivariant linear forms
  has dimension one. Irreducible generic representations are examples;
  irreducibility is not part of the definition.
- §2.3, printed pp.386–387 (PDF pp.21–22): normalized induction from the
  lower standard parabolic of admissible finite-type blocks is again
  admissible of finite type. The proposition attributed to Rodier on p.387
  says that its functional space is one-dimensional if and only if every
  block functional space is. JPSS refer to Rodier for the proof. The present
  statement uses the forward direction together with the admissibility and
  finite-type assertion; it does not formalize that proof.

The source permits any nonarchimedean local field. This interface specializes
to the Library's p-adic fields, finite extensions of `ℚ_p`, because the
canonical induction constructor has that scope. No source-specific erratum
was found in the available project literature and public notes when checked
on 2026-10-25.

## Upper convention and intended proof dependencies

The induction in this statement is the published
`PadicField.canonicalNormalizedProductInduced` from `Induction.BlockFactors`,
using the published `succBlockShape` from `RankinSelberg.MultiplicativityStatement`.
Its left covariance uses the positive half modulus of the actual upper block
parabolic, and the group acts by right translation on its smooth function
carrier. This module imports the parent without changing its Lean/Markdown
pair, imports, block shape, or induction construction.

This is a derived upper-convention interface of the source assertion, not
an identification of the upper and lower induction spaces by definition.
Conjugating the lower parabolic by the permutation matrix that reverses the
ordered blocks while retaining their internal coordinates gives the upper
parabolic with reversed block order. If this matrix is `w`, the map
`f ↦ (g ↦ f(w⁻¹ g))` intertwines the right actions. Its covariance involves
the reversed block family and the transported half modulus: the lower
exponent of `|det g_i|` is the total size of earlier blocks minus that of
later blocks, which is the upper exponent in the reversed order. An actual
representation equivalence therefore transports full Whittaker type, and
quantification over all ordered families supplies the upper formulation.
Constructing and proving this opposite-parabolic comparison is separate work;
this proposition definition does not establish it.

An intended Lean route instead reuses the upper-unnormalized targets
`Langlands.InducedWhittakerTypeStatement` and
`Langlands.InducedFiniteTypeStatement`, with the canonical construction
`PadicField.TopologicalData.normalizedProductHalfAbsorptionEquiv` in
`Induction.BlockCharacterAbsorption`. That equivalence absorbs the half
modulus into scalar twists of the individual blocks. Their characters have
open kernels and are trivial on their upper unipotent subgroups. Full
functional spaces are transported using `Whittaker.twistFunctionalEquiv`.
Finite generation under these scalar twists must hold for arbitrary
representations, not just irreducible ones: the currently published
`Langlands.finite_asModule_twist_iff` in `RankinSelberg.WhittakerTypeTwist`
supplies this via the order equivalence of invariant submodules over the
group algebra. The same module's `isOfWhittakerType_twist_iff` combines these
facts with admissibility. Induced admissibility can reuse
`Parabolic.normalizedInductionAdmissibility` and
`FiniteTensor.isAdmissible_external`.

These are dependencies for the later proof, not hypotheses added to this
statement. This unit introduces no absorption construction, heredity proof,
finite-type proof, admissibility proof, or opposite-parabolic transport.
Stating the proposition does not prove those inputs or their assembly.

## Validation

Exact declaration inspection in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` succeeded with zero errors or warnings,
`statement_returns_prop: true`, and independent universe parameters `uF` and
`uW`. Its only reported axioms are `propext`, `Classical.choice`, and
`Quot.sound`. This compilation and inspection does not prove the proposition.
