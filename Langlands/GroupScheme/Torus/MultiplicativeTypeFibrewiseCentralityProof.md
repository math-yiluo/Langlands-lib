# Fibrewise centrality for homomorphisms from groups of multiplicative type

The theorem `Langlands.GroupScheme.multiplicativeTypeFibrewiseCentrality` proves
`MultiplicativeTypeFibrewiseCentralityStatement.{u}` for every universe `u`. It
uses the published `multiplicativeTypeCentralRigidity` theorem to discharge the
central-rigidity premise of the two fibrewise lemmas.

For both parts of Théorème 5.6, the proof installs the ambient structure
morphism's local finite presentation, quasi-compactness, and
quasi-separatedness hypotheses as instances.

- For 5.6(a), `MultiplicativeTypeCentralityPropagation.exists_open_isCentral`
  uses rigidity to make universal conjugation constant on an open around the
  unit above the selected point. The inverse image of that open along the unit
  section is a neighbourhood in the base. In each connected residue fibre
  above it, the flat surjective product map from two copies of the unit open
  detects commutation on every test scheme. Fibrewise detection gives
  centrality over the neighbourhood.
- For 5.6(b),
  `MultiplicativeTypeFibrewiseCentralityReduction.isCentral_of_fibres_of_centralRigidity`
  compares the conjugation family to the constant family over every test
  scheme. Centrality of the residue fibres gives equality on the residue
  fibres of each parameter scheme. Rigidity gives equality locally, which
  glues and yields commutation on every test scheme.
- For Corollaire 5.5,
  `RelativeMultiplicativeType.isCentral_of_isNormal_of_connectedFibres` uses the
  unit points to deduce geometric connectedness of the ambient group over the
  base. The immersion supplies the monomorphism needed to internalize the
  ambient conjugation action on the normal subgroup. Relative rigidity makes
  this action the identity. The target's local finite type hypothesis is unused
  in this clause.

The proof is an internal derivation of SGA 3, Exposé IX, Théorème 5.6 and
Corollaire 5.5, using the source edition and page locators recorded with the
published statement. [Statement and source](MultiplicativeTypeFibrewiseCentralityStatement.md)
