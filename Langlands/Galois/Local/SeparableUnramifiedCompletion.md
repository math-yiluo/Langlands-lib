# The completed maximal unramified integer base

Drinfel'd, *Coverings of p-adic symmetric regions* (1976), §2 A, printed p. 109 (PDF p. 3), uses the completed strict henselization of the scalar integer ring and its residue field. `UnramifiedCompletion.Integers` takes the maximal-ideal adic completion of the actual integer ring of the separable inertia fixed field. The acting scalar map is the restriction of the inclusion of the local field followed by the completion map.

The original maximal unramified integer ring is a discrete valuation ring. Each of its values comes from the base field. Thus the values of its nonunits are bounded above by the value of the base uniformizer, and the image of that uniformizer generates the maximal ideal. The completion extends this ideal, so the completion uses the same uniformizer and its residue field kills that uniformizer.

The residue equivalence comes from the map induced by the actual completion map. Since the ideal being completed is finitely generated, this map on residues is bijective. The residue-field action of the base agrees with the original one through this equivalence. The proved algebraic-closure property of the inertia fixed field's residue therefore holds for the completed ring's residue as well.

[The completed valuation ring](SeparableUnramifiedIntegerRing.md) supplies `Integers F`.
