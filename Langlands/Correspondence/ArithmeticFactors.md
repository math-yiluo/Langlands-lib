# Arithmetic pair factors on the correspondence domains

Author: Worker 7. This module defines the Weil–Deligne side of the pair-factor
conditions of the local Langlands correspondence for `GL_n(F)`: the pair
L-factor `L(s, X ⊗ Y)` and the pair epsilon factor `ε(s, X ⊗ Y, ψ)` of two
pair classes of the actual local Weil group of a p-adic field `F`. The
L-factor is a definition. The epsilon factor is a relation that depends on a
supplied local-constant system; no system, additive character, measure or
Frobenius element is chosen. The module states no theorem and proves nothing
beyond the well-definedness of `weilPairClass`.

## Definitions

Throughout, `F : PadicField p` carries its canonical topological data, `q` is
its residue cardinality, and `W_F = Weil.Local.localWeilGroup F` is the
published local Weil group.

- `LocalPairClass F` is the published type of isomorphism classes of all
  finite-dimensional complex Weil–Deligne pairs `(r, N)` of `W_F`, of every
  dimension, with covariance character the local norm character. No
  continuity, semisimplicity or parameter condition is imposed; it is the
  domain of the published pair L-factor.
- `weilPairClass F σ` sends a continuous irreducible Weil class `σ` of rank
  `n` (`IrreducibleWeilClass F n` from `Domains`) to the class of the pair
  `(σ, 0)`. It is the published `zeroMonodromy` construction on
  representatives. It is well defined because the published zero-monodromy
  functor carries representation isomorphisms to pair isomorphisms.
- `arithmeticPairLFactor F X Y` is the published
  `WeilDeligne.pairLFactorClass` at the published inertia subgroup
  `localInertia F` and the published geometric Frobenius lift
  `localGeometricFrobenius F` (degree `+1`). On representatives it is the
  rational function `det(1 - X r(Φ) | (ker N)^I)⁻¹` in the variable
  `X = q^(-s)`, for the actual tensor pair `X ⊗ Y` with monodromy
  `N ⊗ 1 + 1 ⊗ N`. Two Frobenius lifts differ by an inertia element, which
  acts trivially on `(ker N)^I`, so the value does not depend on the lift.
  The Library proves this for every Weil–Deligne representation, not only
  for common-closure pairs: `WeilDeligne.rationalLFactor_eq_of_coset`
  (module `Langlands.LocalFactor.WeilDeligne`) gives
  `rationalLFactor A I h = rationalLFactor A I g` for every normal subgroup
  `I` and all `g, h` with `h * g⁻¹ ∈ I`. The published
  `WeilDeligne.pairLFactor A B I g` is `rationalLFactor` of the actual tensor
  of `A` and `B`, so the theorem applies to pair factors of representatives.
  `localInertia F` is by definition the kernel of the degree map of `W_F`,
  so two elements of degree `+1` satisfy the hypothesis. The common-closure
  form is `CommonClosureGamma.eulerPolynomial_eq_of_frobenius`. The Library
  states no version for `pairLFactorClass` on classes; there it follows by
  applying the theorem to representatives. Nothing here depends on this
  independence.

The arithmetic epsilon factor is computed with the published common-closure
local-constant machinery (`LocalFactor.CommonClosure`,
`CommonClosureWeilDeligne`, `CommonClosureGamma`). That machinery works over
the finite intermediate fields `E` of the specified algebraic closure of `F`,
with pairs `Pair F E` of the Weil subgroup fixing `E`, additive characters and
Haar measures on `E`, and a system `ε` satisfying
`NonabelianSystem.IsSystem F eC ε` for a common-closure reciprocity family
`eC`. To use it for `F` itself, this module takes `E` to be the bottom
intermediate field.

- `baseExtension F` is the bottom intermediate field `⊥` as a
  `FiniteIntermediateExtension`, with its inferred finite-dimensionality
  instance. It is not the published `extensionFiniteIntermediate F F id`,
  whose embedding into the closure is chosen and so need not be the identity.
- `IsBaseRestriction F X A`: some representative `B` of `X` has its
  restriction along the inclusion of the Weil subgroup fixing `⊥` equivalent
  to the common-closure pair `A`. The two covariance characters agree by
  definition. The equivalence may change the carrier universe.
- `IsBaseCharacter F ψ ψ'`: `ψ'(x) = ψ(x)` for every `x` in `⊥`, where `x` is
  read in `F` through the field isomorphism
  `IntermediateField.botEquiv : ⊥ ≃ F`.
- `IsBaseReciprocity F e eC`: the `⊥`-component of the reciprocity family
  `eC` agrees with the rank-one candidate `e` (published
  `LocalFactor.RankOne.ReciprocityCandidate`) through the same isomorphism:
  for every `w` in the Weil subgroup fixing `⊥`,
  `botEquiv (reciprocityUnits F eC ⊥ w) = RankOne.reciprocityUnits F e w`.
- `IsBaseEpsilonDatum F ψ X Y ψ' μ A B` conjoins `IsBaseCharacter F ψ ψ'`,
  the published self-duality `CommonClosureSpectral.IsSelfDual F ⊥ ψ' μ`, and
  `IsBaseRestriction` for `(X, A)` and `(Y, B)`.
- `IsArithmeticPairEpsilonFactor F eC ε hε ψ X Y c m`, for a nontrivial
  unitary additive character `ψ` of `F`, a unit `c` and an integer `m`, is
  the conjunction of:
  1. some datum `(ψ', μ, A, B)` with `IsBaseEpsilonDatum` exists, with `A`
     and `B` continuous;
  2. a geometric Frobenius element over `⊥` exists;
  3. for every such datum, all continuity proofs, every geometric Frobenius
     `Φ` over `⊥` and every `s : ℂ`, the published
     `CommonClosureGamma.conditionalPairEpsilonValue` of `(A, B)` at `s`
     equals `c q^(-ms)` (published `RankinSelberg.epsilonMonomial`).

Parts 1 and 2 make part 3 nonvacuous: if a transported character, a
self-dual measure or a continuous transported pair failed to exist, the
relation would be false rather than vacuously true. Part 3 quantifies over
every admissible datum, so the value is not tied to any choice. Its
independence of `Φ` is the published `conditionalEpsilonValue_eq_of_frobenius`.

The value `conditionalPairEpsilonValue` is, by its published definition, the
system's value on the norm twist `(A ⊗ B) ω_s` of the underlying continuous
Weil representation, times `det(-q^(-s) r(Φ) | V^I/(ker N)^I)` on the actual
invariant quotient, for the full tensor monodromy. With a self-dual measure
this is Langlands' convention `ε(s, V, ψ)`.

## Sources and provenance

- Tate 1979, (3.3.2), printed p.14 (PDF p.23): for nonarchimedean `F`,
  `L(V) = det(1 - Φ | V^I)⁻¹` with `Φ` an inverse (geometric) Frobenius,
  determined modulo `I`.
- Tate 1979, (3.4.1), printed pp.14–15 (PDF pp.23–24): the unique function
  `ε(V, ψ, dx)` that agrees with the abelian epsilon in degree one and is
  inductive in degree zero. Tate refers to Deligne 1973, §4, for the proof of
  existence. The four laws of the published `NonabelianSystem.IsSystem`
  (additivity, Haar scaling, induction in degree zero, rank one) and its
  normalized-reciprocity conjunct formalize this characterization in a common
  algebraic closure; the published module, not this one, records its
  sources.
- Tate 1979, (3.6.4), printed p.17 (PDF p.26): Langlands' constant is
  `ε_L(s, V, ψ) = ε_D(V ω_s, ψ, dx_ψ)` with `dx_ψ` self-dual for `ψ`. Hence
  the self-duality conjunct of `IsBaseEpsilonDatum`.
- Tate 1979, (4.1.6), printed pp.20–21 (PDF pp.29–30): for a Weil–Deligne
  representation `(ρ, N, V)` with `V_N = (ker N)^I`,
  `L(V, s) = det(1 - Φ q^(-s) | V_N)⁻¹` and
  `ε(V) = ε(ρ) det(-Φ | V^I/V_N)`.
- Henniart 2002, §1.2, printed pp.588–589 (PDF pp.2–3): `L(s, σ)` is the
  Artin L-function and `ε(s, σ, ψ)` the factor defined by Langlands and
  Deligne, citing Tate 1979, §4. The L-factors have the form `P(q^(-s))⁻¹`
  with `P(0) = 1`, and the epsilon factors the form `α q^(-ms)` with
  `α ∈ ℂˣ`, `m ∈ ℤ`. This is why the L-factor is a rational function of
  `X = q^(-s)` and the epsilon relation takes the witness `(c, m)`.

Source files:

- `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `deligne-1973-local-constants`, SHA-256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`
  (cited through Tate (3.4.1)).

## Design notes

- **Base field.** The common-closure system is indexed by intermediate
  fields, not by `F`. The bottom field `⊥` is isomorphic to `F` by the actual
  `botEquiv`, and the character, reciprocity and pair transports are stated
  through that isomorphism. They are relations, not constructions: each is
  asserted to have a witness (part 1, or the outer existential of a caller)
  and then holds for every witness.
- **Reciprocity.** `IsSystem` already contains the published normalized
  reciprocity condition for `eC`. `IsBaseReciprocity` ties the base component
  of `eC` to the candidate `e` used by the other correspondence conditions,
  so the rank-one epsilon law of the system is evaluated with the same
  reciprocity as the determinant and twist conditions.
- **Universes.** A system `ε : NonabelianSystem.Assignment.{uF, uV}` acts on
  pairs whose carriers lie in `max uF uV`. Parameter classes have carriers in
  `uP`. The pair transport goes through universe-heterogeneous equivalences,
  so callers may take `uV := uP`.

The module imports, and does not copy: `Weil.Local.Assembly`
(`localWeilGroup`, `localInertia`, `localGeometricFrobenius`,
`localNormCharacter`), `Weil.Local.Parameters` (`localZeroMonodromyFunctor`),
`LocalFactor.WeilDelignePair` (`pairLFactorClass`),
`LocalFactor.CommonClosure` (`Extension`, `AdditiveCharacter`, `HaarMeasure`,
`ReciprocityFamily`, `reciprocityUnits`, `weilSubgroup`),
`LocalFactor.CommonClosureWeilDeligne` (`Pair`, `GeometricFrobenius`),
`LocalFactor.CommonClosureSpectral` (`IsSelfDual`),
`LocalFactor.NonabelianSystem` (`Assignment`, `IsSystem`),
`LocalFactor.CommonClosureGamma` (`conditionalPairEpsilonValue`),
`LocalFactor.RankOne` (`ReciprocityCandidate`, `reciprocityUnits`) and
`RankinSelberg.FunctionalEquationStatement` (`epsilonMonomial`). From this
task it uses `Domains` (`IrreducibleWeilClass`, `weilClassForget`) and the
reciprocity names of `OperationCompatibility`.

## Validation

The module compiles in the project Lean service with no errors or warnings.
There is no `sorry` and no new axiom. Every relation returns `Prop`.
