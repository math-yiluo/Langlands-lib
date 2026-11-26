# Decomposition of σ-discrete series into an orbit of discrete series

`Langlands.BaseChange.SigmaDiscreteSeriesOrbitDecompositionStatement.{u,v,uW}`
states the forward implication of the orbit classification for `GL_n`. It
uses a characteristic-zero nonarchimedean local field `F : Type u` and a
nonarchimedean local field `E : Type v`. The hypothesis `IsCyclicAlgebra σ l`
specifies a cyclic field extension `E/F` of arbitrary degree `l` with
generator `σ`. The instance `IsModuleTopology F E` specifies the topology
on `E` as a finite `F`-module.

For `n > 0`, the input is a complex representation `P` of `GL_n(E)` satisfying
`IsSigmaDiscreteSeries σ n P`. The Library predicate requires admissibility,
irreducibility, temperedness and σ-stability. It excludes unnormalized
smooth induction from a smooth σ-stable representation of a proper standard
Levi in the carrier universe of `P`. For comparison with the normalization
in II.3.1, normalized induction is obtained by twisting the Levi action by
the half-modulus before unnormalized induction. The half-modulus of a
standard parabolic is σ-invariant, so this twist preserves σ-stability.
[The Library predicate](PseudoCoefficient.md)

The conclusion gives natural numbers `t` and `m` with `hm : 0 < m` and
`h : t * m = n`, and an irreducible representation `Q` of `GL_m(E)`
satisfying `JacquetLanglands.IsSquareIntegrable Q`. This is square-integrability
modulo the center with unitary central character.

## Period and induction

For every `i : ℕ`, the pullback `Q^{σ^i}` acts by `g ↦ Q(g^{σ^i})`. Lean
forms it by composing `Q` with `entrywiseAut (σ ^ i) m`. An intertwining
isomorphism `Q ≃ Q^{σ^i}` exists exactly when `t ∣ i`. Since `t * m = n > 0`,
`t` is the least positive exponent fixing the isomorphism class of `Q`.
Thus `t` is the orbit length and `σ^t` generates the stabilizer of that
class. The equality `σ^l = 1` gives `t ∣ l`.

`sigmaOrbitProduct σ t hm Q` is the normalized parabolic induction of
the tensor product of `Q, Q^σ, …, Q^{σ^{t-1}}` from the standard parabolic
with `t` blocks of size `m`. It acts on `GL_{t * m}(E)`.
`GeneralLinear.reindex (R := E) (finCongr h)` relabels both matrix indices
via `Fin (t * m) ≃ Fin n`. The proposition precomposes the induced action
with the inverse of this group isomorphism to obtain an action of `GL_n(E)`,
then asserts that this representation is equivalent to `P`.

## Carrier universes

The carrier of `P` and the existential carrier of `Q` both lie in `Type uW`,
independently of `u` and `v`. The induced function space can involve the
field universe `v`. `Representation.Equiv` compares the two representations
across their carrier types and universes.

## Sources

- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory
  of the Trace Formula* (1989), Chapter 1, §2.3, Lemma 2.8, printed p. 17
  (PDF p. 31). Literature ID `arthur-clozel-1989-base-change`.
  SHA-256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
  [Book](https://www.claymath.org/library/cw/arthur/pdf/30.pdf)
- G. Henniart and B. Lemaire, *Changement de base et induction automorphe
  pour GL_n en caractéristique non nulle* (2011), II.4.6, printed p. 88
  (PDF p. 96), for the orbit classification. II.1.3, printed p. 56 (PDF p. 64),
  gives the pullback convention, and II.3.1, printed p. 78 (PDF p. 86), gives
  the normalized product convention. Literature ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
  SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
  [Memoir](https://smf.emath.fr/system/files/2017-08/smf_mem-ns_124.pdf#page=96)
