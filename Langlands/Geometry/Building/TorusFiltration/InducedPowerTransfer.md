# Factoring a degree power through an induced torus

`InducedPowerTransfer.exists_degree_power_factorization` considers a torus
\(T\) over \(k\) that becomes induced over a finite separable extension
\(L/k\). Given a finite Galois splitting extension \(E/k\) containing \(L\),
it constructs an induced \(k\)-torus \(S\) and homomorphisms
\(T \to S \to T\) whose composite is the degree-\([L:k]\) power
endomorphism.

Let \(A\) be the character lattice over \(E\). On the product of copies
of \(A\) indexed by the embeddings \(L \hookrightarrow E\), an automorphism
acts on each value and permutes the indices by postcomposition. The
stabilizer of the structural embedding acts through \(\operatorname{Gal}(E/L)\).
The hypothesis on \(T_L\) supplies a basis permuted by that stabilizer
using `IsInducedTorus.exists_permuted_basis` and
`characterLattice.scalarExtensionGaloisEquiv`. Normality transports the
basis to each embedding, and the resulting coordinate basis is permuted
by \(\operatorname{Gal}(E/k)\).

`torusGaloisLatticeRealization` realizes the product lattice by a torus
and `isInducedTorus_of_equivariant_basis` proves that it is induced.
Summation and the constant-tuple map are equivariant. Descent of
equivariant character maps gives the two torus maps in the opposite
directions. The composite on characters is multiplication by the number
of embeddings, which is \([L:k]\) by separability. Uniqueness of descent
identifies the composite on the torus with that power.

This is the character-lattice form of the restriction and norm
construction in the proof of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Proposition B.6.6, printed pp. 671–672, PDF pp. 702–703.
