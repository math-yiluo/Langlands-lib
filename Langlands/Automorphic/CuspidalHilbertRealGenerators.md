# Genuine smooth cuspidal Hilbert vectors and their original real generators

`CuspidalHilbertSmoothEmbeddingStatement` explicitly retains both
`CuspidalHilbertOrbitCoefficientStatement` and
`Archimedean.HilbertSmoothKernelStatement`. For every arbitrary-universe number
field with the compact `AdeleQuotient` convention, every actual cuspidal operator
realization `T` of `GL_(r+1)`, prescribed unitary central character and supplied
full positive form `b` with its exact canonical determinant-band integral
identity, it asserts `SmoothGeneratorComparison` for the original canonical
embedding and the actual coordinate Hilbert representation.

The generic Prop-valued `SmoothGeneratorComparison π j D ζ` means three things:
every `j(v)` has a genuinely real infinitely differentiable orbit in Hilbert
norm; the original complex-linear map `j` is injective; and
`j(D(X)v) = lieDerivative I π (ζ(X)) (j(v))` for every original real direction
and vector. In this actual specialization `j` is exactly `b.finiteForm.toHilbert`,
`π` is the restriction of the actual full adelic action through the published
mixed-coordinate infinite inclusion, `ζ` is `realLieAlgebraToMatrix`, and `D(X)`
is `T.realization.envelopingAction (envelopingGenerator (complexify X))`.
Thus all real directions at complex places remain in the comparison.
The completion is the original supplied form completion; no form or action is
transported to a different Hilbert space.

`cuspidalHilbertSmoothEmbedding` proves this statement. Its supporting modules
construct `toHilbertSmooth`, the complex-linear restriction of the canonical
embedding to the genuine smooth-vector submodule. Norm smoothness comes from
the explicitly retained smooth-kernel criterion and the smooth actual scalar
diagonal coefficient; unitarity identifies the two-variable orbit kernel with
that coefficient at the relative group element. Injectivity is the published
injectivity of the canonical embedding. The generic codomain restriction and
its injectivity lemma give the same injective smooth embedding.

For the generator identity, an arbitrary source Hilbert vector `w` is mapped
by the identity isometry into the full actual band `L²` space. The exact scalar
orbit-value comparison identifies the source orbit pairing with the actual band
coefficient. Full enveloping covariance of its one supplied smooth coefficient
map identifies the coefficient of `D(X)v` with its first scalar differential.
The published actual real generator formula is the manifold derivative in
direction `gX`, which at the identity is the original matrix direction. The
bounded real-linear functional `inner ℂ w (-)` commutes with the derivative by
the manifold chain rule, since the original source vector is already genuinely
smooth. Inner-product separation for all `w` proves the vector equation. This
proves no bounded extension of a Lie generator to every completed vector.

The generic scalar predicates keep the exact equations visible while avoiding
repeated expansion of the nested original carrier and form-completion instances.
The coefficient value, scalar lift and final vector comparison are separate
modules of this one mathematical unit. The proven statement has free universe
`u`, includes `r=0`, and retains both analytic premises without discharging them.

The provenance is internal composition of the actual band constructions,
published real differential geometry, Hilbert inner-product separation and
manifold chain rule. The included `HilbertSmoothKernelStatement` pair is the
unchanged frozen statement pair of Task7671, whose original-source review is
separate. This consumer assumes that proposition; it does not prove the kernel
criterion. There is no assertion of fixed-level derivative-topology density,
full-group intertwining of independently supplied operator equivalences,
Whittaker uniqueness or unconditional cuspidal operator multiplicity one.
