# Potential semistable reduction over a discrete valuation ring

`Langlands.AbelianScheme.PotentialSemistableReductionStatement` concerns an
abelian variety over the fraction field of a discrete valuation ring. It
asserts existence of a local extension of discrete valuation rings whose
fraction field extends the original fraction field finitely. The two maps
from the original valuation ring to the extended fraction field agree.
The output contains a Néron model and its actual generic identification with
the base change of the given abelian variety.

The geometric special fibre is taken over the algebraic closure of the
new residue field. Its connected component of the identity is represented
by an open subgroup and has a smooth surjective homomorphism to an abelian
variety. The scheme-theoretic kernel of that map is isomorphic to a split
torus of finite rank. These data express semiabelian reduction at the
chosen place above the original closed point. Passing to the geometric
special fibre permits the torus to be split there.

## Provenance

This is the DVR and geometric special fibre formulation of Bosch,
Lütkebohmert and Raynaud, *Néron Models* (1990), §7.4, printed p. 181,
Theorem 1 and the preceding definitions. The source takes a finite Galois
extension and obtains semiabelian reduction at every point above the
original closed point. This statement uses one local extension and its
geometric special fibre.
