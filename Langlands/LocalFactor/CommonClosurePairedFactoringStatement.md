# A common finite Galois bound for two Weil factoring kernels

`Langlands.LocalFactor.CommonClosure.PairedFactoringGaloisBoundStatement`
takes an embedding \(f:F\to E\) of \(p\)-adic fields over \(\mathbf Q_p\) and
arbitrary group homomorphisms \(q_F:G_F\to Q\) and \(q_E:G_E\to R\) from the
absolute Galois groups to finite groups. The universes of \(F\), \(E\), \(Q\),
and \(R\) are independent.

It asserts the existence of a finite Galois extension \(N/F\) in the chosen
algebraic closure of \(F\), represented by `CommonClosure.Extension F`.
Its intermediate field contains the chosen image of \(E\) given by
`extensionIntermediateField F E f`. The subgroup \(W_N\) of \(W_F\), defined by
`CommonClosure.weilSubgroup F N`, lies in the closure in \(W_F\) of the kernel
of \(q_F\circ\mathrm{localProjection}_F\). Its inverse image along
`extensionWeilMap F E f` lies in the closure in \(W_E\) of the kernel of
\(q_E\circ\mathrm{localProjection}_E\). Both closures are represented by
`factoringKernelClosure`.

## Mathematical origin

The bound is a local auxiliary statement for applying Henniart's finite
Galois quotient construction over both fields in a tower. Henniart fixes a
finite Galois extension in §3.1 and applies Brauer induction to its Galois
group in §3.7. See Guy Henniart, *Une preuve simple des conjectures de Langlands
pour GL(n) sur un corps p-adique*, pp. 448 and 451 (PDF pp. 10 and 13), source
`henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

The Weil subgroup of a finite intermediate extension is the inverse image of
its Galois fixing subgroup under the Weil projection. This is the finite
extension construction in John Tate, *Number theoretic background*, (1.1),
p. 3 (PDF p. 12), source `tate-1979-number-theoretic-background`, SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

`CommonClosure.exists_open_normal_le` from `CommonClosureBoundedBrauer` gives
open normal subgroups \(U_F\) of \(G_F\) and \(U_E\) of \(G_E\) whose Weil
preimages lie in the corresponding closed factoring kernels. The Galois map
\(\iota=\mathrm{extensionGaloisMap}(F,E,f)\) is an open embedding, so
\(U_F\cap\iota(U_E)\) is open and has finite index in the compact group \(G_F\).
Its normal core is an intersection of finitely many open conjugates. The
core's fixed field is finite Galois over \(F\) and contains the image of \(E\),
since `extensionGaloisMap_range` identifies \(\iota(G_E)\) with the fixing
subgroup of that image. The core lies inside \(U_F\), which gives the lower
kernel inclusion. For an element of \(W_E\) mapping into \(W_N\),
`localProjection_extensionWeilMap` puts the image of its Galois projection
in the core and hence in \(\iota(U_E)\). Injectivity of \(\iota\) puts the
projection in \(U_E\), which gives the upper kernel inclusion.
