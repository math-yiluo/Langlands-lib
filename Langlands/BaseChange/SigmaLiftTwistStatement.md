# Sigma-lifts and character twists

`Langlands.BaseChange.SigmaLiftTwistStatement` is a proposition definition
stating compatibility of sigma-lifts with character twists. It quantifies over
a nonarchimedean local field `F` of characteristic zero, a commutative
topological `F`-algebra `E` with its module topology, an `F`-algebra
automorphism `σ`, and natural numbers `l` and `n` with
`IsCyclicAlgebra σ l`.

Let `π` and `Π` be admissible complex representations of `GL_n(F)` and
`GL_n(E)` on possibly different complex vector spaces. Suppose that `Π`,
with sigma-intertwiner `A` and constant `c`, is a sigma-lift of `π`.
For every character `ω : Fˣ →* ℂˣ` whose complex-valued underlying map is
continuous, set

```text
ωE = ω ∘ N_{E/F},
πω = twist (ω ∘ det) π,
Πω = twist (ωE ∘ det) Π.
```

For every supplied admissibility proof of each twisted representation,
and every sigma-intertwiner `Aω` of `Πω` whose underlying function on the
carrier of `Π` equals that of `A`, the statement asserts that `Πω` is a
sigma-lift of `πω`, with intertwiner `Aω` and the same constant `c`.

## Library interfaces

In the published `Langlands.BaseChange.TwistedCharacter` API, `τ` and
`τω` denote the representations written `Π` and `Πω` here. The type
`SigmaIntertwiner σ n τ` is the representation equivalence from `τ` to
its pullback along `entrywiseAut σ n` from `Langlands.BaseChange.Norm`.
`IsSigmaLift σ l π hπ τ hτ A c` uses the predicate
`AreConcordant σ l μF μE φ f` from `Langlands.BaseChange.OrbitalIntegral`
to match the tests for the Haar measures `μF` and `μE`.

The norm character is written directly as
`ω.comp (Units.map (Algebra.norm F : E →* F))`. The twists and determinants
use `Langlands.twist` and `GeneralLinear.determinant`. The finite-module
instance is the first conjunct of `IsCyclicAlgebra σ l`. The topology
lemmas for `GL_n(F)` in `LocalFieldTopology` take `F n`, and their
finite-algebra counterparts in `TwistedCharacter` take `F E n`.
`Langlands.BaseChange.PseudoCoefficient` supplies `IsSigmaDiscreteSeries σ n τ`
for the discrete-series statements (`DiscreteSeriesSigmaLiftStatement`,
`SigmaDiscreteDescentStatement`).

## Sources and provenance

The source is Henniart--Lemaire, *Changement de base et induction
automorphe pour GL_n en caractéristique non nulle* (2011), Chapter II,
II.2.9, Remark (4), printed p. 70 (PDF p. 78), with the definition of a
sigma-lift in II.2.7, printed p. 67. Arthur--Clozel, *Simple Algebras,
Base Change, and the Advanced Theory of the Trace Formula* (1989),
Chapter 1, Proposition 6.8(ii), printed p. 59 (PDF p. 73), records
the corresponding compatibility for tempered base change.

HL formulate their remark in the irreducible setting. This statement
uses the admissible distributional extension that the discrete-series statements need.
Twisting a trace inserts the character of the determinant, and the
determinants of norm-associated elements are related by `N_{E/F}`.
At each associated pair, the weights multiply both orbital integrals by
the same scalar. Off the norms, the weighted orbital integrals over `F`
still vanish. This preserves concordance and gives the same constant in
the distribution identity. The statement records this admissible
formulation for a later proof.

## Sigma-lifts, constants and scope

For every pair of Borel Haar measures and every concordant pair of test
functions, `IsSigmaLift` equates the twisted trace of `Π` against `A`
with `c` times the trace of `π`. This is HL's sigma-relèvement.
`SigmaLiftCharacterIdentityStatement` states its equivalence with
`IsShintaniLift` for irreducible admissible representations, with the
same constant. The latter is the Shintani character identity of
Arthur--Clozel, Chapter 1, Definition 6.1.

The definition of `IsSigmaLift` requires `c ≠ 0`. HL II.4.6,
Theorem (1), obtain `c = 1` for the Whittaker-normalized intertwiner.
That normalization is outside the programme's definitions.
Scaling an intertwiner by a nonzero scalar `a` scales its twisted
trace and its lift constant by `a`. Equality of the underlying
operators keeps the same intertwiner normalization in this statement.

HL II.2 allows cyclic algebras, including split products, and II.2.8
reduces the character statements to a field factor. Accordingly `E`
is a commutative ring here. Characteristic zero makes the Library's
separable-characteristic-polynomial regularity agree with HL's
squarefree-characteristic-polynomial regularity, and is the setting
of Arthur--Clozel. HL take `n ≥ 1` in II.2.1, printed p. 61. For `n = 0`
both general linear groups are trivial and the two determinant twists act
by the scalar `1`.

HL II.4.7 uses this twist rule to pass from discrete to essentially
discrete representations. HL's discrete series are irreducible
square-integrable representations with unitary central character,
as encoded by irreducibility and `JacquetLanglands.IsSquareIntegrable`.
HL define the essentially discrete class by character twists.
The Library's `JacquetLanglands.IsEssentiallySquareIntegrable` uses real
`|det|`-power twists. These give the same class because a
continuous character of `Fˣ` is a unitary character times a real
power of the absolute value and unitary twists preserve square-integrability.
