# The tempered square-integrability criterion and discrete series from building data

`Langlands.Aubert.General.RepresentedParabolic.TemperedDiscreteSeriesFromBuildingStatement`
takes one hypothesis at the local-field universe `u`. For every connected
reductive group over a nonarchimedean local field in that universe, building and
integral-model data exist satisfying the one-group clauses of the corrected
Kaletha–Prasad building axioms. The exact hypothesis is
`Langlands.Geometry.Building.GroupAxiomsExistenceStatement.{u}`.
[Building hypothesis](../../Geometry/Building/GroupAxiomsExistenceStatement.md)

The conclusion is the conjunction of three previously defined propositions
at field and representation-carrier universes `u` and `v`.

- A tempered smooth complex representation with a central character is
  square-integrable modulo the center for a given Borel Haar measure exactly
  when its unitary Jacquet part vanishes at every represented proper rational
  parabolic with its Levi, radical and split-component data.
  [Tempered square-integrability criterion](TemperedSquareIntegrableUnitaryPartStatement.md)
- An irreducible smooth complex representation is tempered exactly when it
  embeds into normalized induction from an irreducible representation of a
  rational Levi that is square-integrable modulo its center for every Haar
  measure in the statement.
  [Discrete-series embedding equivalence](TemperedIrreducibleDiscreteSeriesStatement.md)
- An irreducible tempered smooth complex representation admits an invariant
  positive-definite Hermitian form.
  [Unitarizability](TemperedIrreducibleUnitarizableStatement.md)

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, VII.2.4 Lemma, printed p. 230 (PDF p. 236), derives the
criterion from the unitary central character and Casselman's criterion in
VII.1.2. The first assertion of the VII.2.6 Theorem, printed p. 231 (PDF
p. 237), uses VII.2.4 to establish the existence of a discrete-series
embedding. The VII.2.6 Corollary, printed p. 232 (PDF p. 238), obtains
unitarizability. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The implication records how these three Library targets depend on the external
structure used for Casselman's criterion. The Chapter V compact-subgroup inputs
enter through the joint special-compact basis, obtained on available building
data. In the VII.2.4 proposition the test uses all represented proper rational
parabolics. In the VII.2.6 equivalence the embedding witness may use any
represented rational parabolic. The published VII.2.6 uniqueness theorem
has its own proof. The relevant compact-subgroup source is Renard V.5.1–2,
printed pp. 122–123 (PDF pp. 128–129).
