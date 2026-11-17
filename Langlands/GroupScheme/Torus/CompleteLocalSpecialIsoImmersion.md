# Special-fibre isomorphisms are open and closed immersions

Worker 356 and Worker 748.

This module proves the immersion half of the complete-local deformation
statement. Over a complete local noetherian ring `R`, let `G` be an affine
group of finite type and let `H` become diagonalizable after a finite étale
surjective cover. If the actual special fibre of `f : H → G` is an
isomorphism, then the underlying scheme morphism of `f` is both an open
immersion and a closed immersion. The theorem is
`open_and_closed_of_special_isIso_of_finiteEtaleSplit`.

This proof does not require flatness of `G`, or a separate assumption that
its special fibre is of multiplicative type. Those assumptions remain in
the unchanged full target, whose Hom-lifting half is not proved here.

For a split diagonalizable source `D_R(M)`,
`specialIsoCoordinateCertificate f` constructs an explicit idempotent in the
actual coordinate algebra `O(G)`. Finite type over the noetherian base makes
`O(G)` noetherian. The actual special-fibre isomorphism gives a unit
coefficient in each character degree, and it detects membership in multiples
of the maximal ideal through the coordinate map `π : O(G) → R[M]`. The
maximal ideal of a local ring is its Jacobson radical. Worker 748's pure
bialgebra theorem `surjective_and_ker_eq_span_idempotent` therefore gives
surjectivity of `π` and an idempotent generating its kernel. The certificate
records this idempotent and both properties. The actual source-coordinate
comparison translates them into an open and closed immersion of the actual
group schemes. This gives
`open_and_closed_of_special_isIso_diagonalSource`, already over a noetherian
local base without completeness or finite generation of `M`.

`open_and_closed_of_special_isIso_of_isDiagonalizable` chooses a relative
diagonalizable presentation of `H` and compares it with the affine
standard model. Composition with its inverse reduces to the split theorem.
Composition with the original presentation transports the two immersion
properties back to `f`.

For a finite-étale-split source over the complete local base,
`localSplitting` gives a finite étale surjective cover `Spec B → Spec R`
with `B` local and noetherian and `H_B` diagonalizable. The actual pullback
composition comparison is a natural isomorphism of functors, so it preserves
and reflects isomorphisms of the base-changed morphisms.
`specialFibre_baseChange_isIso` applies this fact to the commutative square
of residue-field maps for the local algebra map `R → B`. Thus the special
fibre of `f_B` is an isomorphism. The diagonalizable-source theorem makes
`f_B` an open and closed immersion.

The published cartesian square comparing an actual group-scheme morphism
with its base change has right-hand side the projection `G_B → G`.
That projection is étale and surjective. Both open immersions and closed
immersions satisfy étale-surjective descent, by the published scheme-property
descent interfaces. Hence both properties descend from `f_B` to `f`.

This is an internal derived argument for the second conclusion of Conrad
(2014), Theorem B.3.2(2), pp.288–290. Its implemented route uses the
bialgebra grading and Nakayama argument documented in
`CompleteLocalDeformation/OpenClosed.md`, followed by exact scheme-coordinate
comparisons and descent. It does not use Conrad's formal-flatness and kernel
argument and does not prove the first, Hom-lifting conclusion.
