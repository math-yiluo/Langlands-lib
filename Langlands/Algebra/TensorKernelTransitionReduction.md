# Proof of the tensor-kernel transition reduction for Stacks 00MO

`Langlands.Algebra.tensorKernelTransitionReduction` proves
`Langlands.Algebra.TensorKernelTransitionReductionStatement`, the reduction
step in the proof of Stacks Project Lemma 10.99.14 (tag **00MO**). It uses
the helper modules `Langlands.Algebra.IdealTensorRelation` and
`Langlands.Algebra.IdealTensorBaseChangeRelation`. The route follows the
source proof (localization and the composite surjectivity of Lemmas
10.99.12 (00MM) and 10.99.13 (00MN) for the Tor transition), written with explicit relations instead of Tor.

## Setting

As in the statement: rings \(R,R',S,S'\) forming a commutative square, a
finitely generated ideal \(I\subseteq R\) with \(I'=IR'\), an \(S\)-linear
map \(f\colon M\to M'\) that is a base change along \(S\to S'\), \(S'\) a
localization of \(T=S\otimes_R R'\) at \(W\), flatness of \((R/I)\otimes_R M\)
over \(R/I\), and the elementwise transition hypothesis `htor`.

`productAlgebra` is the algebra structure of \(S'\) over \(T\) from
`Algebra.TensorProduct.productMap`, the structure used in the statement's
localization hypothesis. `productAlgebra_algebraMap_tmul` evaluates it on
\(s\otimes a\). The theorem `reduction` is the statement with explicit
arguments. `tensorKernelTransitionReduction` packages it as the published
proposition.

## Proof of `reduction`

1. *Scalar towers.* \(S\to T\to S'\) and \(R'\to T\to S'\) are scalar towers.
   \(M'\) becomes a \(T\)-module through \(T\to S'\).
2. *\(M'\) is a localization of \(P=T\otimes_S M\).* Let
   \(\psi\colon T\otimes_S M\to M'\) be `LinearMap.liftBaseChange T f`. Its
   composite with \(m\mapsto1\otimes m\) is \(f\), a base change along
   \(S\to S'\). Since \(m\mapsto1\otimes m\) is a base change along \(S\to T\)
   (`TensorProduct.isBaseChange`), `IsBaseChange.of_comp` shows that \(\psi\) is a base change along \(T\to S'\). By
   `isLocalizedModule_iff_isBaseChange`, \(\psi\) is a localization at \(W\).
3. *Comparison with \(R'\otimes_R M\).*
   `Algebra.IsPushout.cancelBaseChange` gives an \(R'\)-linear isomorphism
   \(e\colon T\otimes_S M\cong R'\otimes_R M\), and
   \(\psi(e^{-1}(1\otimes m))=f(m)\).
4. *Relations in \(P\).* Choose generators \(g_1,\dots,g_r\) of \(I\)
   (finite generation). Their images generate \(I'\) (`span_mapGen`). Let
   \(\sum_k g_k p_k=0\) in \(P\). Then \(\sum_k g_k e(p_k)=0\) in
   \(R'\otimes_R M\). The relation lemma `sum_tmul_mem_relationSpan`
   (flatness of \((R/I)\otimes_R M\)) puts \(\sum_k g_k\otimes e(p_k)\) in
   the span of the elements \(\sum_k g_k\otimes(1\otimes z_k)\) with
   \(\sum_k g_k z_k=0\) in \(M\). The map
   \(\Phi=\psi\circ e^{-1}\) sends each of these to
   \(\sum_k g_k\otimes f(z_k)\), which is zero by `htor`. Hence
   \(\sum_k g_k\otimes\psi(p_k)=0\) in \(I'\otimes_{R'}M'\).
5. *Injectivity.* By `relations_of_isLocalizedModule`, the same holds for
   every relation \(\sum_k g_k x_k=0\) in \(M'\). Then
   `rTensor_injective_of_relations` gives injectivity of
   \(I'\otimes_{R'}M'\to R'\otimes_{R'}M'\).
6. *Flatness modulo \(I'\).* \((R'/I')\otimes_{R'}P\) is isomorphic, through
   \(e\) and two `TensorProduct.AlgebraTensorModule.cancelBaseChange`
   isomorphisms, to \((R'/I')\otimes_{R/I}((R/I)\otimes_R M)\). This is flat
   over \(R'/I'\) as a base change of a flat \(R/I\)-module. So it is flat
   (`Module.Flat.of_linearEquiv`). `flat_of_isLocalizedModule` passes
   flatness to the localization \((R'/I')\otimes_{R'}M'\).

The ideal \(I\) is required to be finitely generated. No locality or
Noetherian assumption, or finiteness assumption on either module, is used.

## Source and authorship

This proof reuses the complete draft by Worker 251, with proof checking and
companion Markdown corrections by Worker 439. The registered original is
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
file `00MD.html`, Lemmas 10.99.12–10.99.14 (tags 00MM, 00MN, 00MO).
The result proves the published reduction proposition, with six independent
universes; applying the separate local flatness criterion 00ML to obtain
full flatness over \(R'\) is outside this module.
