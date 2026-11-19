# Simple stratum intertwining

`Langlands.BushnellKutzko.simpleIntertwining` proves
`Langlands.BushnellKutzko.SimpleIntertwiningStatement`. The source is
Bushnell–Kutzko (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
Theorem (1.5.8), printed pages 44–46, and the scalar convention (1.4.6),
printed page 36. The Lean proof covers both cases with the original
hypotheses and independent field and vector-space universes.

In the scalar case, the bottom critical exponent forces the generated
algebra to be the scalar algebra. Every ambient unit then commutes
with the stratum element, and the neighborhood is the identity subset.
In the finite case, write \(d=-(r+k)>0\). Every neighborhood unit and
its inverse belong to the hereditary order, and their commutators
belong to the stratum's error lattice. Conjugation by either preserves
the stratum coset, giving the inclusion of the double coset in the
formal intertwining set.

Purity gives a finite extension \(E=F[\beta]\) acting on \(V\).
An endomorphism in the adjoint kernel commutes with this action by
induction in the generated algebra. `LatticeChain.relativeLatticeChain`
views the same lattice subsets over the spectral integer ring of \(E\).
`radicalFiltration` over \(E\) puts the identity in the product of
opposite steps. Restricting those endomorphisms to \(F\) puts the
identity in the corresponding product of centralizer lattices. The same
radical-filtration theorem over \(F\) gives exhaustiveness of the
ambient endomorphism filtration.

To bound the critical-index set, the proof chooses an \(F\)-linear
section on the commutator image and extends it to the ambient
endomorphism space. The step-zero lattice embeds in the endomorphisms
of the zeroth lattice over the base integer ring and is finitely
generated. The images of its generators lie in a common filtration
step. Uniformizer periodicity then sends a sufficiently deep
filtration step into step one under the section. Each element of the
adjoint lattice at that depth is the sum of a centralizer element in
step zero and its commutator lift in step one. This argument adapts the
critical-index bound in Worker 206's Task 7754 draft.

The single-lattice lift uses the critical bound at \(k+1\) and the
opposite-step product. Multiplication into step zero and back expresses
an element below the required depth as a centralizer element plus an
element one step deeper. Removing the centralizer element preserves
the commutator. The opposite-step product also identifies the shifted
intersection lattice at depth \(m\) with \(Q^mN_k\). At \(m=d\) this
identifies the neighborhood with the subgroup of units congruent to
one in the shifted intersection lattice.

The reverse inclusion is implemented as an induction on depth. It uses
exhaustiveness to pick starting depths for an intertwining unit, its inverse,
and the stratum element. The single-lattice lift gives the first centralizing
approximation. To refine it, the current centralizing unit is viewed
as an \(E\)-linear equivalence. `exists_mixed_adjoint_lift` uses the
adjoint relation for the intertwining unit to give a preimage made
up of two translated corrections and a deeper error. Subtracting this
preimage leaves a centralizing error. The proof absorbs it into a fresh
centralizing unit and applies the two corrections to increase depth.
The inverse filtration bound holds throughout the double coset. Once the
depth exceeds the bound required for the final error, the quotient of
the approximation by the current unit belongs to the neighborhood.
This terminates the induction after finitely many corrections.

The centralizing unit approximation uses scalar perturbations by distinct
powers of a uniformizer. These powers lie at arbitrarily large depths.
The nonzero characteristic polynomial of the negative of the centralizing
endomorphism has finitely many roots, so a power at the required depth gives
an invertible perturbation.
