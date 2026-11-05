# Concrete projective adelic points as the full local product

`AdelicProjectiveComparisonStatement` states the full-product and compact
Hausdorff conclusions of Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed p.10, Example 4.3. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The original example assumes n > 0. The statement includes n = 0 as a derived
extension of these comparison and compactness assertions. It makes no density
or non-discreteness claim in dimension zero.

The target is the conjunction of the curve/function-field and number-field
clauses. In each clause the scheme is the actual existing polynomial-Proj
projective space over the original field. The source topology is the arithmetic
spread topology of its concrete projective model over the original outside-S
integer ring with the constructed canonical generic-fiber isomorphism. There is
no assumed model, assumed generic-fiber isomorphism, assumed properness or
assumed local integrality in the statement's inputs.

The map is the published actual coefficient restriction at every place, and the
target topology is the full product of the independently constructed local
scheme-point topologies. The conjunction requires that this actual map be a
homeomorphism and that the actual adelic point space be compact and Hausdorff.
The number-field target retains all infinite factors. The curve target retains
finite constants, the specified rational-function field action, its compatible
scalar tower and potentially inseparable finite extensions. The common universe
is arbitrary and the initial finite set may be empty.

The actual projective models and their generic-fiber isomorphisms are supplied by
`AdelicProjectiveModels`. Their properness permits specialization of the proper
all-place comparison and proper adelic compactness, while separatedness and
independent local Hausdorffness supply the remaining topological conclusion.
This is a proposed statement, not its proof. Rational-point density, the
nonclosed/non-discrete diagonal for positive dimension, and the special
projective-line affine subspace-topology and non-local-compactness conclusions
are separate obligations of the parent program.
