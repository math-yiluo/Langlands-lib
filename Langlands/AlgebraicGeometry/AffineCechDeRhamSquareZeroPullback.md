# Degree-one pullback from local lifts

Let \(X\) and \(Y\) be schemes over \(\operatorname{Spec}R\) with affine open
covers \(U\) of \(X\) and \(V\) of \(Y\), an index map \(\beta\) from the
indices of \(U\) to those of \(V\), and an ideal \(I\) of \(R\). For a tuple
\(\sigma\) of indices of \(U\) write \(U_\sigma\subseteq X\) for the
intersection of the charts \(U_{\sigma(k)}\) and
\(V_{\beta\sigma}\subseteq Y\) for the intersection of the charts
\(V_{\beta(\sigma(k))}\); for a pair, \(U_{ij}=U_i\cap U_j\) and
\(V_{\beta(i)\beta(j)}=V_{\beta(i)}\cap V_{\beta(j)}\).
`tupleSections` is the section algebra on such an intersection, and
`restrictSections` and `restrictCochain` restrict from the intersection of a
subtuple to the intersection of the full tuple.

`LocalPullbacks I β` describes \(R\)-algebra maps
\(s^\sigma_k\colon\Gamma(Y,V_{\beta\sigma})\to\Gamma(X,U_\sigma)\) on every
tuple intersection, indexed by a vertex \(k\) of \(\sigma\). The vertex
selects which local lift supplies the pullback. The maps commute with
restrictions that keep the selected vertex (`restrict_sections`), and
different vertices give maps agreeing modulo \(I\,\Gamma(X,U_\sigma)\)
(`congruent`).

Assume \(I^2=0\). A degree-zero cochain \(h\) for \(V\) has components
\(h_{\beta(i)}\in\Gamma(Y,V_{\beta(i)})\); `cochainZero` sends it to the
cochain for \(U\) with components
\(s^{(i)}_0(h_{\beta(i)})\in\Gamma(X,U_i)\). A degree-one cochain \((a,b)\)
for \(V\) has function components
\(a_{\beta(i)\beta(j)}\in\Gamma(Y,V_{\beta(i)\beta(j)})\) and one-form
components \(b_{\beta(i)}\in\Omega_{\Gamma(Y,V_{\beta(i)})/R}\).
`cochainOne` sends it to \((a',b')\) with
\[
b'_i=(s^{(i)}_0)^{*}b_{\beta(i)}\in\Omega_{\Gamma(X,U_i)/R},\qquad
a'_{ij}=s_0\bigl(a_{\beta(i)\beta(j)}\bigr)
+\iota_{s_1-s_0}\bigl(b_{\beta(j)}|_{V_{\beta(i)\beta(j)}}\bigr)
\in\Gamma(X,U_{ij}),
\]
where \(s_0=s^{(ij)}_0\) and \(s_1=s^{(ij)}_1\) are the pullbacks
\(\Gamma(Y,V_{\beta(i)\beta(j)})\to\Gamma(X,U_{ij})\) for the vertices
\(i\) and \(j\). The argument of the contraction is the one-form
\(b_{\beta(j)}\) restricted to the target overlap \(V_{\beta(i)\beta(j)}\),
an element of \(\Omega_{\Gamma(Y,V_{\beta(i)\beta(j)})/R}\), and `contraction`
is the difference contraction
\(\iota_{s_1-s_0}\colon\Omega_{\Gamma(Y,V_{\beta(i)\beta(j)})/R}
\to\Gamma(X,U_{ij})\) of `AffineCechDeRhamSquareZeroHomotopy`, with
\(\iota_{s_1-s_0}(dx)=s_1(x)-s_0(x)\). These are the lemmas
`cochainZero_apply`, `cochainOne_fst` and `cochainOne_snd`. The Library's
Čech differential is \((\partial b)_{ij}=b_j-b_i\) on restricted forms, and
the total differential is \((a,b)\mapsto(\partial a,\partial b-da,db)\);
the sign of the correction is chosen for this convention.

`cochainOne_D0` shows that the corrected map sends the total boundary of a
degree-zero cochain \(h\) for \(V\) to the total boundary of
`cochainZero h`. `cochainOne_mem_cocycles` shows that it sends cocycles to
cocycles. The closed-form component follows from naturality of the exterior
derivative. On a pair \((i,j)\), the affine homotopy identity for the closed
form \(b_{\beta(j)}|_{V_{\beta(i)\beta(j)}}\) gives the compatibility of the
pulled-back form and function components. On a triple \((i,j,k)\) the
contractions of \(b_{\beta(k)}\) restricted to
\(V_{\beta(i)}\cap V_{\beta(j)}\cap V_{\beta(k)}\) telescope, and the
remaining difference of pullbacks is the contraction of the equality
\(\partial b=da\) on the pair \((\beta(j),\beta(k))\) of the last two
vertices. Thus the function component also satisfies the cocycle condition.
`cocyclePullback` is the resulting linear map on cocycles, and
`LocalPullbacks.pullbackH1` is the induced map \(H^1\to H^1\) on the
quotients by total boundaries; `pullbackH1_mk` computes it on a class.

`pullbackH1_eq_of_congruent` compares two systems \(L,M\) whose maps
\(s^\sigma_k\) and \(t^\sigma_l\) agree modulo the extended ideal for all
vertices \(k,l\). On a cocycle \((a,b)\) for \(V\) the two corrected
cocycles differ by the total boundary of the degree-zero cochain for \(U\)
with components
\(\iota_{s^{(i)}_0-t^{(i)}_0}(b_{\beta(i)})\in\Gamma(X,U_i)\), so the
induced maps on `H1` agree.

`pullbackH1_maps_hodgeF1` treats a system whose two overlap maps coincide
on every pair, \(s^{(ij)}_1=s^{(ij)}_0\). Then the overlap contractions
vanish, the class of \((0,b)\) for a compatible closed form \(b\) for \(V\)
goes to the class of the compatible closed form
\(\bigl((s^{(i)}_0)^{*}b_{\beta(i)}\bigr)_i\) for \(U\), and `hodgeF1`
maps into `hodgeF1`.
`exists_functionPrimitive_of_pullback_closedForm_mem_hodgeF1` gives a
partial converse for a compatible closed form \(b\) for \(V\). Let
\(c=(a',b')\) be the corrected cocycle of \((0,b)\); since
\(s_0(0)=0\), its function component is
\(a'_{ij}=\iota_{s_1-s_0}\bigl(b_{\beta(j)}|_{V_{\beta(i)\beta(j)}}\bigr)\).
Suppose the pullback of the class of \((0,b)\) lies in the first Hodge step,
so that it is also the class of \((0,\omega)\) for a compatible closed form
\(\omega\) for \(U\). Then \(c-(0,\omega)\) is a total boundary: there is a
degree-zero function cochain \(h\) for \(U\), with components
\(h_i\in\Gamma(X,U_i)\), such that
\[
c-(0,\omega)=D_0h=(\partial h,dh).
\]
The degree-one function components of the two sides, on pairs, give
\[
(\partial h)_{ij}=\iota_{s_1-s_0}\bigl(b_{\beta(j)}|_{V_{\beta(i)\beta(j)}}\bigr)
\in\Gamma(X,U_{ij})
\]
for every pair \((i,j)\). The theorem asserts the existence of such an
\(h\).

The construction implements, in the sign convention above, the local-lift
calculation in the proof of Kai-Wen Lan, *Arithmetic compactifications of
PEL-type Shimura varieties*, revised 14 March 2021, Proposition 2.1.6.4,
printed pp. 133–135 (PDF pp. 161–163). The comparison of signs with that
proof is explained in `AffineCechDeRhamInfinitesimalMorphism.md`. The
retained source is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
