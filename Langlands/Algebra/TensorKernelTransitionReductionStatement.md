# Tensor-kernel transition reduction for Stacks 00MO

`Langlands.Algebra.TensorKernelTransitionReductionStatement` states the
reduction step in the proof of Stacks Project Lemma 10.99.14, tag **00MO**.
The Tor groups are written as ideal tensor kernels. The hypotheses of 00MO
give the two hypotheses of Lemma 10.99.10, tag **00ML**, for \(R'\), the
extended ideal \(I'=IR'\) and the module \(M'\). This module defines a
proposition; it does not prove it, and it does not state the flatness
conclusion of 00MO.

## Statement

Let \(R\to R'\), \(R\to S\), \(S\to S'\) and \(R'\to S'\) be maps of
commutative rings forming a commutative square. Let \(I\subseteq R\) be a
finitely generated ideal, \(I'=IR'\), \(M\) an \(S\)-module and \(M'\) an
\(S'\)-module, with an \(S\)-linear map \(f\colon M\to M'\). Assume:

1. \(S'\) is the localization of \(S\otimes_R R'\) at a submonoid \(W\),
   through the canonical map \(s\otimes r'\mapsto s\,r'\);
2. \(f\) identifies \(M'\) with \(S'\otimes_S M\);
3. \((R/I)\otimes_R M\) is flat over \(R/I\);
4. for every finite family \(a_1,\dots,a_n\in I\) and \(m_1,\dots,m_n\in M\)
   with \(\sum_k a_k m_k=0\), the element
   \(\sum_k a_k\otimes f(m_k)\) of \(I'\otimes_{R'}M'\) is zero.

Then \(I'\otimes_{R'}M'\to R'\otimes_{R'}M'\) is injective, and
\((R'/I')\otimes_{R'}M'\) is flat over \(R'/I'\).

## Lean encoding

- The square is given by the five `Algebra` instances and
  `IsScalarTower R S S'`, `IsScalarTower R R' S'`. The second tower says that
  the structure map \(R\to S'\) is \(R\to R'\to S'\), and the first that it is
  \(R\to S\to S'\). Together they say that the square commutes.
- The canonical map \(S\otimes_R R'\to S'\) is
  `Algebra.TensorProduct.productMap` of the two `IsScalarTower.toAlgHom`
  maps. Its value on \(s\otimes r'\) is the product of the images. Hypothesis 1 is
  `IsLocalization W S'` for the algebra structure given by this map. The
  structure is local to that hypothesis (`letI`), so no global instance is
  added.
- `Module R M` with `IsScalarTower R S M` is the restriction of the
  \(S\)-action along \(R\to S\). The modules `Module R' M'` and
  `Module S M'` with `IsScalarTower R' S' M'` and `IsScalarTower S S' M'`
  are restrictions of the \(S'\)-action.
- `IsBaseChange S' f` says that \(s'\otimes m\mapsto s'\,f(m)\) is a bijection
  \(S'\otimes_S M\to M'\). This is the source's \(M'=M\otimes_S S'\), with the
  scalar factor written first.
- `I.map (algebraMap R R')` is \(I'=IR'\). In hypothesis 4,
  `⟨algebraMap R R' (a k), Ideal.mem_map_of_mem _ (a k).2⟩` is the image of
  \(a_k\) in \(I'\), and the sum is taken in `I.map (algebraMap R R') ⊗[R'] M'`.
- `LinearMap.rTensor M' (I.map (algebraMap R R')).subtype` is the tensor of
  the inclusion \(I'\to R'\) with the identity of \(M'\). Both conclusions use
  the forms of the corresponding hypotheses of
  `Langlands.Algebra.IdealLocalFlatnessCriterionStatement` (00ML), with
  \(R'\), \(M'\) and \(I'\) in place of \(R\), \(M\) and \(I\).
- `(R ⧸ I) ⊗[R] M` and `(R' ⧸ I') ⊗[R'] M'` carry their canonical
  quotient-ring actions through the first factor. They identify with
  \(M/IM\) and \(M'/I'M'\) (`TensorProduct.quotTensorEquivQuotSMul`).
- The six types use six independent universes.

## Relation to the source

Source 00MO considers a commutative square of local homomorphisms of
Noetherian local rings, a proper ideal \(I\subset R\), a finite
\(S\)-module \(M\), \(I'=IR'\) and \(M'=M\otimes_S S'\). It assumes that
\(S'\) is a localization of \(S\otimes_R R'\), that \(M/IM\) is flat over
\(R/I\), and that \(\operatorname{Tor}_1^R(M,R/I)\to
\operatorname{Tor}_1^{R'}(M',R'/I')\) is zero, and it concludes that \(M'\)
is flat over \(R'\).

Its proof first shows that \(M'/I'M'\) is flat over \(R'/I'\). It then
reduces, by 00ML, to the vanishing of
\(\operatorname{Tor}_1^{R'}(M',R'/I')\). It proves this vanishing using
Lemmas 10.99.12 and 10.99.13 and the localization hypothesis. The present
proposition states exactly these two intermediate claims, the hypotheses of
00ML. The steps that prove them (base change of flatness, Lemma 10.39.7;
flatness of a localization; exactness of localization; Lemmas 10.99.12 and
10.99.13) hold for arbitrary commutative rings and modules. The local,
Noetherian, properness and finiteness hypotheses of 00MO are used only when
00ML is applied to \(R'\to S'\), \(I'\) and \(M'\): there \(R'\) and \(S'\)
must be Noetherian local with \(R'\to S'\) local, \(I'\ne R'\) (which follows
from \(I\ne R\) and locality of \(R\to R'\)), and \(M'\) must be finite over
\(S'\) (which follows from finiteness of \(M\) over \(S\)). Combined with
00ML, the present proposition therefore gives 00MO, and those hypotheses
are omitted here. Finite generation of \(I\), automatic for Noetherian
\(R\), is kept.

Tor is translated as follows. For a commutative ring, the exact sequence
\(0\to I\to R\to R/I\to 0\) and symmetry of Tor identify
\(\operatorname{Tor}_1^R(M,R/I)\) with the kernel of
\(I\otimes_R M\to M\), and similarly over \(R'\) with \(I'\) and \(M'\).
These connecting identifications are natural for the map of short exact
sequences over \(R\to R'\) and for \(f\). Hence the source's transition map
is the restriction to these kernels of
\(I\otimes_R M\to I'\otimes_{R'}M'\), \(a\otimes m\mapsto a\otimes f(m)\).
Every element of \(I\otimes_R M\) is a finite sum \(\sum_k a_k\otimes m_k\),
and it lies in the kernel exactly when \(\sum_k a_k m_k=0\). Hence the
transition map is zero exactly when hypothesis 4 holds. Vanishing of
\(\operatorname{Tor}_1^{R'}(M',R'/I')\) is the injectivity in the first
conclusion (compare the Markdown of 00ML). The flatness of \(M/IM\) and
\(M'/I'M'\) is expressed as in 00ML. No abstract Tor object is formalized.

The registered original is `stacks-algebra-flatness-criteria-2026-10-22`,
folder SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
file `00MD.html`: Lemma 10.99.14 (00MO), statement and proof, with
Lemmas 10.99.12 and 10.99.13 cited there. The reduction is an internal,
source-derived formulation of the intermediate claims of that proof, as
explained above; it is not a verbatim statement of 00MO. No errata note
for this source was found on 2026-10-27.
