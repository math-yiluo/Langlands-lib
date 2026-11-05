# Proof of Bochner integrated-action preservation and naturality

Worker 116 proves
`Langlands.Analysis.IntegratedIsometricNaturalityStatement` with theorem
`Langlands.Analysis.integratedIsometricNaturality`, in independent group
and ambient-space universes. This is currently a private development
proof; publication requires the unchanged target and imports in the
Library and a separate exact-target proof task.

After introducing the actual group, Banach action, measure, scalar weight
and every explicit measurability, norm and integrability hypothesis, fix
a closed invariant complex submodule P. Closedness supplies the
`CompleteSpace P` instance. For x:P define the actual P-valued weighted
orbit Φ(x,g)=f(g)π(g)x; invariance and closure under scalar multiplication
provide its subtype membership proof.

Apply `LinearIsometry.integral_comp_comm` to the subtype inclusion P→E.
The underlying vector of the P-valued integral is exactly the ambient
Bochner weighted-orbit integral, hence exactly the constructed T x.
The P-valued integral's subtype property proves hTP, preservation of P.
The proof supplies hTP as the existential witness required by the target.

For an arbitrary ambient submodule Q and an actual complex-linear
isometric equivalence U:P≃Q satisfying the displayed group intertwining
equation, compose U with the subtype inclusion Q→E. This is a linear
isometry L:P→E between complete source and ambient target; no completeness
instance on Q is used. Complex linearity of U and its group intertwining
identify L(Φ(x,g)) with f(g)π(g)(Ux) pointwise. The same integral theorem
for L identifies the integral of this expression with L applied to the
P-valued integral. The first inclusion identity also identifies the
subtype vector of T x with that integral. Substituting these identities
gives exactly U(Tx)=T(Ux) in E, using the supplied hTP for the left subtype.

The pinned integral theorem is unconditional for linear isometries
between complete spaces: isometry reflects integrability, so it also
handles the total integral's zero convention. Here ambient weighted-orbit
integrability has already been proved by the imported constructor under
the target's explicit hypotheses; the proof does not add a hidden
measurability, separability or operator-norm continuity assumption.

The proof implements the internal Bochner route documented in the
statement's English Markdown. It does not construct the analytic
application's group topology, Haar measure, Dirac sequence, compactness,
symmetry, strong approximation or automorphic Hilbert realization.
It proves no decomposition or multiplicity conclusion on its own.
