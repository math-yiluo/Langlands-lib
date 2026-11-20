# Central character of the complex standard module

This is an internal computation with the Library's ordered PBW basis and
Harish–Chandra projection. If a functional annihilates strictly upper matrix
units on the left and acts by specified weights on diagonal units, it evaluates
a central element by the lower Verma character at those weights. Centrality
forces the PBW terms to have weight zero for the diagonal operator whose
entry at the zero-based index \(p\) is \(-p\). Terms beginning with strictly
upper units vanish under the functional. Among the remaining terms, weight
zero forces every unit to be diagonal, so successive application of the
functional's diagonal rule evaluates the Harish–Chandra polynomial.

The two block inclusions are obtained from the published scalar-extension Lie
equivalence. The image of each block center commutes with the generators from
its own block by centrality and with the other block because the Lie brackets
across the blocks vanish.

Evaluation at the identity of the complex standard module kills the strictly
upper units on either block by the published derivative formula. For the
diagonal unit at position \(p\), the two blocks use
\(\tfrac12(\kappa_p(1)-\mathrm{i}\kappa_p(\mathrm{i}))\) and
\(\tfrac12(\kappa_p(1)+\mathrm{i}\kappa_p(\mathrm{i}))\).
Here \(\kappa_p(1)=2t_p+n-1-2p\) and
\(\kappa_p(\mathrm{i})=\mathrm{i}\ell_p\), where \(t_p\) is the inducing
exponent and \(\ell_p\) the inducing weight. The resulting weights are
\(t_p+\ell_p/2+\rho_p\) on the first block and \(t_p-\ell_p/2+\rho_p\) on
the conjugate block. The normalized lists before adding \(\rho\) are precisely
`zExponent` and `zBarExponent`.

The published infinitesimal-character theorem gives a scalar action on the
standard module. Evaluation detects that scalar because some compact-finite
function has nonzero value at the identity. If every such value vanished,
compact right translation would give vanishing on the entire compact subgroup.
The published determination of principal-series functions by their restriction
to that subgroup would then contradict nontriviality. Applying the PBW formula
at a function with nonzero value gives the lower Verma character. The
comparison with the upper character identifies the scalar for any weight
whose shifted list is a permutation of the corresponding normalized exponent
list.
