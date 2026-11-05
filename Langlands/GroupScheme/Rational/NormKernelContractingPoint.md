# Norm-kernel cocharacter points escaping every compact set

This internal construction supplies actual rational points for the compact
restriction converse. It uses the integral correction defined in
`NormKernelCocharacter`, together with the actual-root-system adapter
`IsStandardCocharacter.normKernelCocharacter_of_relativeRootSystem` in
`NormKernelStandardCocharacter` and the published intrinsic cocharacter
evaluation and point-topology results.

The preliminary evaluation identity identifies the torus evaluation followed
by its inclusion with the literal `cocharPoint` of the composite cocharacter.
If all restricted ambient rational characters pair to zero with a cocharacter,
each of their values on any evaluated point is the zeroth integer power,
hence one. The evaluated point therefore belongs to the actual common norm
kernel.

The compact-escape proof takes a closed torus inclusion, a character with
positive integral pairing, and a field unit whose field powers converge to
zero. The inverse image of an ambient compact set in the torus is compact,
because the point map is a closed embedding. The character's field-valued
image of this compact set is closed and omits zero. On the successive
cocharacter powers its value tends to zero: it is the corresponding positive
integer power of the parameter's field powers. Those values eventually leave
the closed image, so the original powers eventually leave the ambient compact
set.

`normKernelCocharacterPoint` evaluates the integral Weyl correction at the
given unit. Its values belong to the actual common norm kernel. If the
original cocharacter is standard for a proper simple-root face, one simple
root outside that face has positive pairing with the correction. Applying the
escape proof to that character gives compact escape. The proper-face premise
is essential here; no nonempty-root premise is used.

The parameter is any field unit with powers tending to zero. The construction
does not select a particular uniformizer. Such a parameter is available over
every nonarchimedean local field by the published
`exists_unit_tendsto_pow_zero`. Uniform contraction of both dynamic radicals
for this same literal point is provided by `CocharacterContraction`.

The module proves geometric helpers, with the displayed closedness,
splitness, finite actual Weyl group, and relative-root assumptions. It asserts
no Iwahori basis or representation-theoretic conclusion. Its provenance is
the implemented intrinsic character-evaluation and compact-image argument,
using `CocharacterUniformizerEvaluation`, `RepresentedSubgroup`, and
`NormKernelStandardCocharacter`.
