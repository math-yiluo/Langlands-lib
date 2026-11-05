# Finite residual coset stabilization

This internal supporting construction formalizes the finite-coset mechanism in
Renard, *Représentations des groupes réductifs p-adiques* (2026), V.5.3,
printed pp.124–125 / PDF pp.130–131. It does not construct an actual reductive
Cartan decomposition or its simultaneous small levels.

An antitone natural-valued function on a finite orthant admits a finite
frontier preserving its value below every point. The implemented proof applies
Dickson's lemma to the minimal elements of the graph in the product of that
orthant with the natural numbers. Antitonicity forces the two values to agree.
The empty coordinate type is included.

For a compact open subgroup `K`, the right `K`-cosets met by `U f`, with
`U ≤ K`, form a finite set. The proof takes a continuous image of the compact
set `K` in the discrete coset space and then a subset. Applying the preceding
frontier lemma to the cardinalities of a decreasing family of these finite
sets gives equality of the entire coset sets at a finite frontier. No residual
element is required to normalize `K`.
