# Full kernels of descended torus quotient maps

This internal construction concerns an arbitrary extension of fields `K/k`,
with both fields in an arbitrary common universe. It assumes an affine group
scheme `G` over `k`, an actual homomorphism `r : G → R`, and a supplied torus
quotient `q : G_K → Q`. Its full kernel is represented by a closed inclusion
`i : U → G_K`, where `U` is smooth, connected and unipotent. An actual target
isomorphism `e : R_K ≅ Q` and the equality `r_K ≫ e.hom = q` are inputs.

`torusQuotientKernelDescent` returns the actual ground-field scheme kernel
`kernel r` with its canonical inclusion, an isomorphism
`(kernel r)_K ≅ U` commuting with those inclusions, and the same target
isomorphism and recovery equality. It proves that `R` is a torus and that `r`
is the fppf quotient by that full kernel. The inclusion `kernelι r` satisfies
the existing `LeviSubgroup.IsGeometricUnipotentRadical` predicate, including
comparison with the actual radical after extension to an algebraic closure.
There are no algebraicity, finiteness, separability, perfection or
characteristic assumptions on the field extension.

The generic helpers first compare kernel ranges on every relative test scheme.
Cancellation of the target isomorphism identifies the kernel of `r_K` with the
kernel of `q`. The canonical kernel base-change isomorphism and the existing
comparison with any monomorphic full-kernel representative then recover `U`,
with an explicit inclusion compatibility law. This also rewrites the supplied
fppf quotient using the actual base change of `kernelι r`.

For the field construction, the existing torus-quotient recognition theorem
first makes `i` a represented radical over `K`. The source recovery isomorphism
transports this predicate to the extended ground kernel. Closedness of the
ground kernel follows from the separated torus target; the existing field
reflection theorem then recovers smoothness, connectedness, unipotence,
normality and greatestness over `k`. Fpqc reflection recovers the fppf quotient.
Finally the existing torus-quotient recognition theorem gives the actual
algebraic-closure radical comparison.

This is derived infrastructure from the Library's actual kernel, represented
subgroup, torus transport, quotient reflection and radical recognition APIs.
No external assertion is transcribed. It assumes the descended map and the
extension-field quotient with its kernel geometry; constructing those inputs,
proving the kernel split and proving the host split geometric radical theorem
remain separate obligations.
