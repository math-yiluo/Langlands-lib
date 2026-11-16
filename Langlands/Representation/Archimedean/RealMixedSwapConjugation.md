# Conjugating real rank-three intertwiners by signed reversal

This internal supporting unit derives a transport principle from
`RealMixedSwapLie`, `RealMixedSwapSigned` and the actual compact and infinitesimal
actions of the Library's real standard modules. It uses no external existence,
classification or irreducibility theorem.

Let \(V(ds)\) denote the complex vector space of compact-finite functions in
`realStandardModule 3 ds`. Suppose
\[
 e_1:V(ds)\simeq_{\mathbb C}V(ds'),\qquad
 e_2:V(es)\simeq_{\mathbb C}V(es')
\]
are complex-linear equivalences. The definition `conjugateMap` sends a
complex-linear map \(T:V(ds')\to V(es')\) to
\[
 e_2^{-1}\circ T\circ e_1:V(ds)\longrightarrow V(es).
\]
This definition itself imposes no action identities on the equivalences.

The transport theorems assume a common natural number \(q\), and assume that
each \(e_i\), after coercion to a function on \(\mathrm{GL}_3(\mathbb R)\),
is the signed reversal
\[
 (S_qf)(g)=\operatorname{sign}(\det g)^q
 f\bigl(w(g^t)^{-1}\bigr)
\]
defined in `RealMixedSwapSigned`. Both equivalences and these function identities
are explicit inputs.

`signedEquiv_map_rep` proves
\[
 e(R_kf)=\operatorname{sign}(\det k)^q R_k(e f)
\]
for the compact action. The previously proved identity has the right translation
on the other side; multiplying by the same sign power converts it to this
orientation, since that scalar has square one.
`signedEquiv_map_lie` proves
\[
 e\bigl(R_Xf\bigr)=R_{-X^t}(e f)
\]
for the infinitesimal action on real matrix directions. It applies the signed
right derivative identity to the smooth function underlying a standard-module
element. In Lean the action is written `realStandardLie ... (1 ⊗ₜ X)`.

`isRealStandardIntertwiner_conjugateMap` assumes that \(T\) is an
`IsRealStandardIntertwiner` between the reversed modules and proves the same
property for the conjugated map. Applying the injective map \(e_2\) to each
desired identity reduces the compact case to the same sign scalar on both
sides and the infinitesimal case to the same direction \(-X^t\) on both sides.
The existing stability lemmas supply the source action membership witnesses.
No inverse-direction surjectivity assertion is needed in this argument.

Finally, `injectiveIntertwinerExists_conjugate` transports
`RealInjectiveIntertwinerExists 3 ds' es'` to
`RealInjectiveIntertwinerExists 3 ds es`. Injectivity is the composition of
the injectivity of \(e_1\), \(T\) and \(e_2^{-1}\).

This unit constructs neither the signed-reversal equivalences for particular
block parameters nor an intertwiner for the reversed pair. Those remain
necessary inputs before this transport can be used to prove the host mixed
swap statement.
