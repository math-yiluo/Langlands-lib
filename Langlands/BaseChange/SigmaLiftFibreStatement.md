# Fibres of sigma-lifting for essentially discrete series

`Langlands.BaseChange.SigmaLiftFibreStatement` is a proposition
definition. Let `F` be a nonarchimedean local field of characteristic
zero, and let `E` be a field with an `F`-algebra structure, a topological
ring structure and the module topology. Let `σ : E ≃ₐ[F] E` and
`l n : ℕ` satisfy `IsCyclicAlgebra σ l`.

Suppose `π` and `π'` are irreducible admissible essentially
square-integrable complex representations of `GL_n(F)`, and `Π` is
an irreducible admissible complex representation of `GL_n(E)`.
For any sigma-intertwiners `A` and `A'` of `Π` and constants `c` and
`c'`, if `Π` is a sigma-lift of `π` with `(A,c)` and of `π'` with
`(A',c')`, then there is a character `κ : Fˣ →* ℂˣ` such that

```text
κ(N_{E/F}(x)) = 1 for every x : Eˣ,
π' ≅ twist (κ ∘ det) π.
```

The two representations over `F` can have carriers in different
universes. The isomorphism is a Mathlib `Representation.Equiv` and
its existence is stated with `Nonempty`. The norm is
`Units.map (Algebra.norm F : E →* F)`, and the twist and determinant
are `Langlands.twist` and `GeneralLinear.determinant`.

## Library interfaces

The published `Langlands.BaseChange.TwistedCharacter` API uses `τ` for the
representation written `Π` here. In `SigmaIntertwiner σ n τ`, the target
of the representation equivalence is the pullback of `τ` along
`entrywiseAut σ n` from `Langlands.BaseChange.Norm`. The lift predicate
is `IsSigmaLift σ l π hπ τ hτ A c`. It uses
`AreConcordant σ l μF μE φ f` from `Langlands.BaseChange.OrbitalIntegral`
to match the tests for the Haar measures `μF` and `μE`.
`Langlands.BaseChange.PseudoCoefficient` supplies `IsSigmaDiscreteSeries σ n τ`
for the σ-discrete series statements in Task 7449.

## Sources and scope

The primary source is Henniart--Lemaire, *Changement de base et
induction automorphe pour GL_n en caractéristique non nulle* (2011),
Chapter II, II.4.8, Lemma (2), printed p. 90, with proof on p. 91
(PDF pp. 98–99). The same fibre assertion appears in II.4.6,
Theorem (2), printed p. 88. In characteristic zero see also
Arthur--Clozel, *Simple Algebras, Base Change, and the Advanced
Theory of the Trace Formula* (1989), Chapter 1, §6.3, the final
paragraph of the discrete-case proof of Theorem 6.2, printed
p. 57 (PDF p. 71), and Proposition 6.7, printed p. 59
(PDF p. 73).

HL allow `π'` to be any irreducible generic representation.
This statement specializes it to essentially square-integrable
`π'`, as required for the programme's cuspidal application.
Irreducible essentially discrete representations of `GL_n` are
generic. The characters in the conclusion are HL's `K(E/F)`,
defined in II.1.3, printed p. 56, by triviality on
`N_{E/F}(Eˣ)`. The Lean conclusion records the underlying
monoid homomorphism and its norm-triviality.

The converse at the level of the literature is the character
twist rule. A `κ` in `K(E/F)` has trivial norm character over `E`,
so the twist over `E` is `Π ⊗ 1 = Π`. `SigmaLiftTwistStatement` states
that rule with explicit continuity, twisted admissibility and
intertwiner data.

HL's discrete series are irreducible square-integrable
representations with unitary central character, corresponding to
irreducibility together with `JacquetLanglands.IsSquareIntegrable`.
Their essentially discrete representations are twists of these by
characters of the determinant. The Library's
`JacquetLanglands.IsEssentiallySquareIntegrable` allows real
`|det|`-power twists. This gives the same class, since a
continuous character of `Fˣ` factors as a unitary character
times a real power of the absolute value and unitary twists
preserve square-integrability.

## Sigma-lifts and constants

`IsSigmaLift` means that for all Borel Haar measures and all
concordant test functions, the twisted trace of `Π` against
the specified intertwiner is the specified constant times
the trace of the representation over `F`. This is HL II.2.7,
printed p. 67. `SigmaLiftCharacterIdentityStatement` states
the equivalence with the Shintani character identity
`IsShintaniLift`, following HL II.2.9 and Arthur--Clozel's
Definition 6.1.

Both constants are nonzero by `IsSigmaLift`. HL obtain constant `1` for
the Whittaker-normalized intertwiner in II.4.6, Theorem (1). The Lean
statement uses the supplied choices `(A, c)` and `(A', c')`. For an
irreducible admissible `Π`, Schur's lemma makes the two intertwiners scalar
multiples. Scaling an intertwiner by a nonzero scalar scales its lift
constant by that scalar, so the two lift identities can use a common
intertwiner in the source argument.

## Field hypotheses and proof dependency

The field assumption on `E` matches HL II.4.6–II.4.8 and the
global-method proof in II.6.1. HL refer there to
Arthur--Clozel §6.3 for characteristic zero. The `CharZero F`
hypothesis also identifies HL's squarefree-characteristic-
polynomial regularity with the Library's separable-
characteristic-polynomial regularity. HL take `n ≥ 1` in II.2.1,
printed p. 61. For `n = 0`, both general linear groups are trivial
and the two irreducible representations over `F` are one-dimensional.
They are isomorphic, so the trivial character suffices.

The finite-module instance is the first conjunct of `IsCyclicAlgebra σ l`.
The topology lemmas for `GL_n(F)` in `LocalFieldTopology` take `F n`,
and their finite-algebra counterparts in `TwistedCharacter` take `F E n`.

HL explicitly state that Lemma II.4.8 is independent of the
existence theorem II.4.6. Its proof uses the orthogonality
relations for discrete-series characters on the elliptic
set, character twists, and the nonvanishing of an
essentially discrete character at an elliptic norm.
A later proof task can follow this route without invoking
the existence or descent statement.
