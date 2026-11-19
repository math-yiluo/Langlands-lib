# Splitting a finite étale algebra by sections

The internal theorem `exists_algEquiv_pi_of_sections` uses one geometric
fibre of a finite étale algebra over a Noetherian domain. Suppose each point
of that fibre is the specialization of an algebra map back to the base.
The product of these maps is an isomorphism onto the finite power of the
base indexed by the fibre points.

The proof applies the Library's geometric fibre conservativity theorem to
the map of spectra. An algebra map from a finite power of the base into the
geometric point field factors through exactly one coordinate. The coordinate
idempotents sum to one, so some idempotent maps to one. Multiplication by
that idempotent forces the map to equal evaluation at its coordinate followed
by the structural field map. Under the affine algebra-point comparison,
the product map therefore induces the chosen bijection of geometric fibres.
The proof includes the empty fibre and the empty product.

Conversely, `exists_section_of_algEquiv_pi` uses the same factorization of a
field-valued point through one coordinate to obtain a section of a split
algebra through the given point.
