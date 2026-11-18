# Finite-group scalar two-cocycle torsion

These internal derived lemmas use an explicit finite-product calculation. For a
finite group acting multiplicatively on a commutative group, multiply the scalar
two-cocycle identity over its third variable. Left multiplication permutes the
index set, so the group-order power is the coboundary of the product cochain.
This construction supplies an actual trivializing cochain.

Coboundaries respect pointwise multiplication and integer powers. The integer
Bezout coefficients therefore trivialize a cochain if two coprime powers have
actual trivializing cochains. In particular a cocycle power prime to the group
order can be a coboundary only when the cocycle itself is a coboundary. No
normalization assumption is needed for these identities.

The intended application is the Sylow fixed-field argument behind Gille and
Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), Lemma 4.5.14
and Proposition 4.5.13(2), printed pp.104–105 (PDF118–119), registered as
`gille-szamuely-central-simple-algebras-galois-cohomology-2006`. These lemmas are a
direct calculation; they do not yet construct a cocycle from an actual algebra,
identify Brauer multiplication, or prove an algebra splitting criterion.
