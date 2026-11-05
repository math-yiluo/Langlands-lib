# Actual tangent complex and enveloping actions on original adelic functions

This internal construction fixes an arbitrary number field `F`, an affine
group scheme `G/F` and a proof that `G` is smooth of relative dimension `d`.
The local instances in the file select exactly the previously constructed
`smoothChartedSpace F G hsmooth` and `smoothLieGroup F G hsmooth`.
They install no global choice of atlas.

The real Lie algebra is the actual identity tangent
`GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)`,
with its actual left-invariant-vector-field bracket. Its complexification is
the actual tensor product `ℂ ⊗[ℝ] GroupLieAlgebra ...`; the domain of both
enveloping actions is Mathlib's actual universal enveloping algebra of this
complex Lie algebra. Each center action restricts along the inclusion of
`Subalgebra.center ℂ` of that associative enveloping algebra.

All actions retain the explicit hypothesis `hcalc :
smoothVectorFieldCommutator ...`. This generic scalar manifold commutator
has not been proved by this construction. The input real Lie actions are
`realPlotSmoothLieAction` and `realFinitePlotSmoothLieAction`, acting on the
unchanged original infinite plot-smooth functions and finite-smooth
rational-invariant continuous adelic functions. The finite carrier uses its
standard additive group from `Module.addCommMonoidToAddCommGroup ℂ`.

`ComplexLieExtension.lie` and `.enveloping` produce the complex Lie and
unital complex algebra homomorphisms. The pure-tensor formulas give
`D(z ⊗ X) = z • D(X)`, and each real-generator formula recovers exactly the
previous actual tangent derivative, with positive right orbit `x * h`.
No arbitrary replacement differential or abstract action is supplied.

Every original finite slice intertwines the complex Lie actions. Its proof
uses induction on the actual tensor product, the original real differential
slice identity and complex linearity. Every slice also intertwines the full
enveloping actions. The proof represents an enveloping element by a tensor
algebra element using `RingCon.mkₐ_surjective`, then uses tensor algebra
induction. The scalar case uses the scalar endomorphism action, the generator
case uses complex Lie intertwining, and multiplication uses composition of
endomorphisms. The same identity for the center follows by restriction.

Faithfulness of all original finite slices and their finite-right-translation
formula prove that every enveloping differential commutes with every finite
right translation. Consequently, each specified finite subgroup fixing the
input also fixes its enveloping derivative. `HasFiniteLevel` is preserved
using exactly the same compact open subgroup.

This is an internal construction. The tensor algebra induction adapts
`Langlands.Global.ArchimedeanGL.envelopingLeftTranslation` in
`Langlands/Global/ArchimedeanEnvelopingLawsProof.lean` by Worker 72. The
existing finite-slice identity is
`Langlands.Automorphic.finiteSmoothSlice_envelopingAction` in
`Langlands/Automorphic/EnvelopingAction.lean`. The real derivative, smooth
atlas and original descent constructions retain their contributing authors, Workers 94, 274, 383 and 1203.
General-linear comparison, exponential-curve comparison, uniform growth,
reduction and finite-volume assertions remain separate obligations. The
explicit generic scalar commutator premise is required throughout.
