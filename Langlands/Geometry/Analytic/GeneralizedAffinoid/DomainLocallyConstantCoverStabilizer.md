# Open stabilizers and locally constant descent on actual finite covers

Worker 56 connects the direct spectrum-input locally constant descent to the
constructed open function stabilizers. The input is an actual invariant
represented domain, an actual finite domain cover, and locally constant
functions on the entire representing spectra of the components. Coefficients
form an arbitrary set in an independent universe, with no topology assumption.

The acting group is the existing `finiteFamilyOpenSubgroup H c.obj`. It is
the largest open subgroup inside `H` that preserves every represented
component locus. All component algebras, spectra, structural quotient maps,
topologies and actions remain those of the imported domain construction.

`finiteCoverSpectrumFunctionStabilizer` constructs the finite intersection
of the full open subgroups fixing the component functions. Its membership
lemma gives exactly the pointwise fixedness equations for the original
inverse section-pullback actions. Openness is inherited from the compact
spectrum stabilizer construction and finite intersection. No fixedness
equations or compatibility are needed to construct this open subgroup.

`finiteCoverComponent_smul` exposes the equivariance equation of the
original component quotient as an equality of points in the target locus.
It is obtained by evaluating the existing equivariant component morphism.
`finiteCoverComponentSpectrumOperator` is its original continuous spectrum
operator, with the unchanged spectrum carrier explicit in its type.

When the functions satisfy all equal-image fiber equations,
`finiteCoverSpectrumFunctionStabilizer_glue` proves that their common open
stabilizer equals the full open subgroup fixing the locus function
constructed by `spectrumLocallyConstantGlue`. For one inclusion, the
original finite-cover quotient supplies a component-spectrum preimage of
every target point. Component equivariance and the gluing evaluation law
then give fixedness at that point. For the converse, the same equivariance
and evaluation law transfer target fixedness to every component-spectrum
point. The equality concerns the entire two open subgroups inside the
same common acting group.

`finiteCoverSpectrumFunctionStabilizer_restrict` applies this equality to
the restrictions of an existing locus function, using the proved
gluing-after-restriction identity.

This is an internal consequence of the imported actual finite-cover
equivariance, quotient surjectivity, locally constant gluing and compact
function stabilizers. It uses no injectivity of a structural spectrum
map. Empty loci and empty covers, trivial scalar valuations, positive
polyradii and nilpotent affinoid quotients remain allowed. It supplies
compact-domain local action data for constant coefficients; it does not
construct the analytic étale site or prove smoothness for arbitrary
analytic sheaf sections.
