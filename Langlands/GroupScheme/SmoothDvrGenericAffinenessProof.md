# Smooth DVR groups with affine generic fibre are affine

`Langlands.GroupScheme.smoothDvrGenericAffineness.{u}` proves the unchanged
`Langlands.GroupScheme.SmoothDvrGenericAffinenessStatement.{u}` for every
universe `u`, without additional hypotheses. The DVR, specified fraction field
and actual group scheme retain the quantifiers of that proposition.

The proof first applies
`SmoothDvrGenericAffinenessDescent.smoothDvrGenericAffineness_of_strictHenselian`.
That reduction constructs a faithfully flat strictly henselian DVR extension
in the same universe, transports the original generic-fibre affineness through
the originally specified fraction field, and descends affineness of the actual
base-changed scheme. Thus it suffices to prove the criterion over a henselian
DVR with separably closed residue field.

For that local case, affineness of the actual generic structure morphism gives
affineness of its total scheme, because its base is an affine spectrum.
Smoothness gives flatness of the original group. The explicit construction
`FlatPidAffinization.groupStructure G` supplies a group structure on the exact
canonical affinization `canonicalAffinization G.X`. Its compatibility theorem
`toAffinization_isMonHom G` makes the exact canonical map
`toCanonicalAffinization G.X` a homomorphism.

The actual constructor `smoothDvrFibreDenseAffineOpen R G.X.left G.X.hom`
then supplies an affine open and, for every point, a generization in that open
with the same base image. Restricting that property to points of the closed
fibre supplies precisely the density hypothesis of
`SmoothDvrLocalAffinization.isAffineHom`. That theorem proves the canonical
map to the spectrum of global functions is an isomorphism and gives affineness
of the original structure morphism.

Both local construction inputs are therefore discharged by actual
constructions in this proof. The local assembly proves smoothness from a
principal chart and Henselian translations, then an open immersion from the
generic monomorphism criterion. The special-fibre section injection makes
its open subgroup image dense, and the arbitrary-ambient open-subgroup
closedness theorem makes it closed. The generic and special fibres then give
the isomorphism. No finite-generation hypothesis on global sections or full
Raynaud affineness assertion is used.

This is the smooth case of Prasad–Yu, *On quasi-reductive group schemes*,
Proposition 3.1, author-preprint p.5, implemented using the internal
closed-image and section-injection route for the final special-fibre step.
The affine-neighbourhood input is constructed from
Bosch–Lütkebohmert–Raynaud, *Néron Models* (1990), §6.4 Lemma 4 and the
following paragraph, printed p.155. The paired helper modules document the
individual constructions and the alternative final argument.
