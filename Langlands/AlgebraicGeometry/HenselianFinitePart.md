# Finite clopen parts over a Henselian local ring

For a Henselian local commutative ring `R`, `finitePart f` constructs an actual
open subscheme `U` of `X` that is closed in `X`, finite over `Spec R`, and
contains every point of the closed fibre of `f : X → Spec R`. The morphism
is assumed locally of finite type, quasi-compact, locally quasi-finite, and
separated. All schemes and the base ring range over an arbitrary universe `u`.

`exists_finite_affine_neighborhood` applies
`HenselianFiniteNeighborhood.exists_idempotent_finite_away` to a prime above
the maximal ideal in an affine chart. The equivalence between a principal
open and the spectrum of its localization, together with the finite
algebra-map criterion, makes that open finite over `Spec R`. This argument
uses the proved Henselian lifting and étale quasi-finite decomposition
described in the companion commutative-algebra module.

`exists_finite_clopen_neighborhood` transports the chosen principal open
through an affine chart into `X`. Its composite with `f` is finite and
therefore proper. Since `f` is separated, the open inclusion itself is
proper. Its image is consequently closed as well as open, and its restricted
map to `Spec R` is finite.

The closed fibre has finitely many underlying points by local
quasi-finiteness and quasi-compactness. `finitePart` chooses one of the
preceding neighborhoods for each such point and takes their union `W`.
This union is closed because it is finite. The preimages of the chosen
neighborhoods cover `W` by finitely many clopen opens; their structure maps
are finite. The proved finite-cover gluing theorem
`GenericFiniteness.IsFinite.of_forall_isClosed_of_iSup_eq_top` gives
finiteness of `W → Spec R`. The same argument includes an empty closed
fibre, when the union and its indexing set are empty.

The returned subtype carries precisely `IsFiniteClosedFibrePart f U`;
no finite-part existence premise is supplied. This is an internal derived
construction from the named proved algebraic, affine, properness and
finite-cover results. It does not itself construct group quotients or
assert the host reductive isogeny theorem.
