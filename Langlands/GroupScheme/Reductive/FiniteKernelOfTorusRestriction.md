# Finite full kernels from a finite maximal-torus restriction

This derived support module works over every field in every universe. Its
first three results work over an algebraically closed field, and the final
result descends to an arbitrary field. It concerns actual group-scheme
homomorphisms and retains the full possibly nonsmooth kernel.

`kernel_isFinite_of_cocharacter_injective_algClosed` assumes a connected
reductive source, a separated target, and that no nonzero actual cocharacter
of the source is killed by the homomorphism. It proves that the actual kernel
is finite. The proof takes the smooth reduced identity component of the
kernel. Every cocharacter of that component maps to a killed cocharacter of
the source and is therefore zero. The published no-cocharacter criterion
makes the component unipotent. Its composite inclusion into the source is
normal on all test schemes, so the source's trivial unipotent radical makes
that inclusion trivial. Monicity implies that the component has a singleton
underlying space. Its image is open in the original kernel. The published
open-singleton finiteness criterion then makes the original kernel finite,
including its nilpotent structure.

`cocharacter_injective_of_finite_torus_restriction_algClosed` assumes a
smooth connected affine source, an actual maximal torus inclusion, and a
commuting square with an actual finite homomorphism between commutative group
schemes and a closed target inclusion. Every cocharacter of the source is
conjugate into the specified maximal torus. The square and the closed target
inclusion identify the torus cocharacter as killed by the finite map.
Cancellation through a finite homomorphism on maps from the smooth connected
multiplicative group makes that cocharacter zero.

`kernel_isFinite_of_finite_torus_restriction_algClosed` combines the two
results for a connected reductive source. The target inclusion is closed;
the target group is separated; and the torus restriction is finite. No
flatness or surjectivity of the ambient map is assumed or concluded, and no
smoothness or connectedness of its kernel is assumed.

`kernel_isFinite_of_finite_torus_restriction` proves the same full-kernel
conclusion over an arbitrary field with the same hypotheses. The proof
base-changes the connected reductive source, its maximal torus, the closed
target inclusion and the finite torus map to an algebraic closure. The
algebraically closed result makes the kernel there finite. The actual
kernel-base-change isomorphism identifies that kernel with the pullback of
the original kernel. Finite-morphism descent along the faithfully flat
quasi-compact field extension proves the original kernel finite.

`isIsogeny_of_finite_torus_restriction` further assumes that the ambient
homomorphism is flat, surjective and quasi-compact. Finite-kernel fpqc descent
then makes the ambient homomorphism finite, and it is an isogeny. These
ambient hypotheses are explicit; no centrality is asserted.

The provenance is internal deduction from the published reduced subgroup,
normality, no-cocharacter unipotence, maximal-torus conjugacy, finite-map
cancellation, and open-singleton finiteness results. Only the auxiliary
identity component passes through reduction; the concluding finite
structure morphism is that of the original kernel.
