# Inner type A Hasse injectivity reduces to locality of reduced norms

`NumberFieldInnerTypeASimplyConnectedGaloisHasseKernelStatement` says
that any cocycle of a simply connected absolutely almost-simple group
with inner type A on a finite Galois cover of a number field is
trivial if it is trivial on the pullback cover at every place. Inner
type A is the existing condition on the full type A Cartan matrix
and trivial absolute Galois star action of a Tits index.

`numberFieldInnerTypeASimplyConnectedGaloisHasseKernel_of_reducedNormLocality`
proves this statement given `NumberFieldReducedNormLocalityStatement`.
The inner type A classification realizes the group as the actual
reduced-norm-one group of a central simple algebra. The affine
norm obstruction gives a unit-group primitive on the given cover
and a scalar \(a\) over the number field. At each completion \(K\),
a maximal ideal of \(K\otimes_F L\) gives a finite residue field
of \(K\) receiving the original coefficient field \(L\). A finite
Galois overfield of that residue field gives a comparison field. The
construction is `CentralSimpleUnits.exists_finiteGalois_over_baseChange`.
Local triviality on the actual pullback to \(K\) then makes the
image of \(a\) a reduced norm over \(K\). Reduced-norm locality
makes \(a\) a norm over \(F\), and the global correction produces
a norm-one primitive on the original cover.

This implements the reduction in Platonov and Rapinchuk, *Algebraic
Groups and Number Theory* (1994), §6.7, pp. 356–357. The input
`NumberFieldReducedNormLocalityStatement` is the local-to-global
part of equation (6.39).
