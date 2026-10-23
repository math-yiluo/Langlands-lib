# Harish-Chandra compact-coefficient equivalence on product Levis

Authors: Worker 200 (forward implication and assembly), Worker 252 (converse
and dual averaging), and Worker 237 (split contraction and gap vanishing).

`Langlands.CuspidalSupport.leviHarishChandraTheorem` proves exactly
`LeviHarishChandraTheorem.{uF,uV}`. For every prime `p`, actual
`PadicField.{uF} p`, compatible topological data `T`, rank `n`, block shape `B`
and smooth complex representation `A` of `B.Levi F.Carrier`, it establishes
the equivalence between vanishing Jacquet coinvariants for every proper
refinement and compact support of coefficients against smooth algebraic-dual
vectors of the restriction to `determinantUnitSubgroup T B`.

The proof splits the rank. At zero it uses
`leviHarishChandraRankZero`, whose singleton-group proof is explained in
`HarishChandraBoundaryProof.md`. At positive rank it pairs the forward
compact-support theorem with `leviHarishChandraConverseTheorem`. The former
uses finite bounded-gap Cartan double cosets and smoothing of the functional;
the latter uses determinant-unit contracting powers and Jacquet kernels. The
paired Markdown of each proof describes those arguments.

The forward helper's explicit Cartan premise is discharged by
`Langlands.GeneralLinear.Cartan.cartanDecomposition` from
`Langlands.Group.GL.CartanProof`, specialized to the field and its value group.
Thus the closing theorem has no Cartan premise or other theorem-valued input.
It retains independent field and representation-carrier universes. No
admissibility, irreducibility, finite length, finite dimension, semisimplicity,
central character or positive-rank hypothesis is imposed.

The original source is Bernstein and Zelevinsky, *Representations of the group
GL(n,F) where F is a non-Archimedean local field* (1976), literature id
`bernstein-zelevinsky-1976-representations-gln`, §§2.39–2.40 (p.26) and
§§3.18, 3.20–3.23 (pp.34–35), especially Theorem 3.21. Its “finite”
representation condition means compact smooth-dual coefficients. Its inverse
group argument in the coefficient convention gives the same compact-support
condition because inversion is a homeomorphism. The forward proof implements
the source's contraction and Cartan support argument directly for averaged
orbits; the converse uses the compression/Jacquet-kernel route described in
`HarishChandraConverseProof.md`. Rank zero is the elementary empty-product
extension specified in the Library statement, rather than an additional
positive-rank source claim.
