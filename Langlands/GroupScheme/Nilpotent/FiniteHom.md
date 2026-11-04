# Nilpotence reflected by finite homomorphisms

Author: Worker 1487. Internal derived interface.

`HasCentralBasePointKernel p` says that the kernel of the actual homomorphism
on base-field points is contained in the abstract centre of the source point
group. It does not assert centrality of the full scheme-theoretic kernel.

For a finite homomorphism whose source is smooth connected affine, conjugation
by a kernel point has the same composite with the homomorphism as the identity.
The existing `finiteHom_cancel` theorem identifies those two actual group-scheme
maps. Their evaluation on each base-field point proves centrality.

Apply this to the actual algebraic-closure base change of a finite homomorphism.
Smoothness, affineness, connectedness and finiteness persist. Mathlib's central
kernel nilpotence theorem then reflects nilpotence of the target geometric point
group to the source. This proves `IsNilpotentGroupScheme.of_finiteHom`.
Neither surjectivity nor flatness is needed, and no field or characteristic
restriction is imposed.

The final lemma first base changes target unipotence and applies the existing
unipotent-points nilpotence theorem, then uses this reflection result. Its target
is geometric nilpotence of the source. The source is smooth connected affine;
the target is affine and locally of finite type, with its unipotence supplied
as a hypothesis.

These are internal deductions from published finite-homomorphism cancellation,
actual inner automorphisms, geometric connectedness, and abstract group theory.
They do not assume the no-torus theorem or maximal-torus preservation.
The helper does not prove the no-torus theorem or general reflection of
unipotence under isogenies.
