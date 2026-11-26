# Local maps of witnessed generators

`WitnessedGenerator.exists_conj_localMap` applies `RelativeWeilGroup.exists_conj_of_isLocalRelativeWeilMap` to the finite places above \(v\), reciprocity candidates and local maps carried by two witnessed generators.

`RelativeWeilGroup.localComponentConjEquiv` intertwines restriction along conjugate maps by the action of the conjugating element. If \(\iota'(g)=t\iota(g)t^{-1}\), the intertwining map from \(S\circ\iota\) to \(S\circ\iota'\) is \(S(t)\), with inverse \(S(t^{-1})\). `ExactGrothendieckGroup.ofRepresentation_eq_of_equiv` then gives `localExactClass_eq_of_conj`. Together these results show that the exact restriction class of a continuous representation is independent of the choice between the maps of two witnessed generators.

These identities allow the two generators in the pair-factor clauses of `Langlands.Global.PoleComparison.RelativeIsometryFactorStatement` to be restricted along a common local map.
