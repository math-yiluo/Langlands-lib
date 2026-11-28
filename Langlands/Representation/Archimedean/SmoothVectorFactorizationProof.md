# Smooth-vector factorization for a closed linear Lie group: the proof

The theorem `Langlands.Archimedean.smoothVectorFactorization` proves
`Langlands.Archimedean.SmoothVectorFactorizationStatement`. Let \(G\) be a Lie group with a
closed linear realization \(j : G \to A^\times\), let \(\mu\) be a left Haar measure on \(G\), and
let \(\pi\) be a jointly continuous representation of \(G\) on a complex Banach space \(E\). Then
every smooth vector \(v\) is a finite sum
\[
v=\sum_i\int_G k_i(g)\,\pi(g)w_i\,d\mu(g),
\]
where the \(w_i\) are smooth vectors and the \(k_i\) are smooth, compactly supported kernels
supported in a given neighbourhood \(U\) of \(1\). Each integrand is Bochner integrable.

The proof works first on a subgroup \(G\le A^\times\) with an exponential Lie algebra \(\mathfrak g\)
(`Langlands.LinearLieGroup.IsExpLieAlgebra`) and its exponential charts. It then transports the
result to an abstract Lie group through its closed linear realization. The group-specific
private lemmas below are in the section `ExponentialCharts` of this file. Two general private
helpers come before that section: `iteratedDeriv_compCLM` (a continuous linear map commutes with
iterated derivatives) and `eq_of_dual_unitBall` (two vectors agreeing under every functional of
norm at most \(1\) are equal).

Throughout, \(\mathbb R^d\) means `Fin d → ℝ` with its Lean norm, the sup norm
\(\|t\|=\max_j|t_j|\). So the closed ball of radius \(r\) about \(0\) is the cube \([-r,r]^d\).

## 1. The line derivatives of a smooth vector

Fix \(X\in\mathfrak g\) and a smooth vector \(v\), and put \(F(t)=\pi(\exp tX)v\)
(`exponentialOrbit`). Then \(F\) is \(C^\infty\) on \(\mathbb R\)
(`contDiff_exponentialOrbit`). Since \(F(t+s)=\pi(\exp sX)F(t)\) and a bounded operator commutes
with iterated derivatives (`iteratedDeriv_compCLM`), we get
\[
F^{(p)}(s)=\pi(\exp sX)\,u_p,\qquad u_p=F^{(p)}(0)
\]
(`iteratedDeriv_exponentialOrbit`). Each \(u_p\) is again a smooth vector
(`smoothVector_iteratedDeriv_exponentialOrbit`). In the chart at \(g\), the orbit of \(u_p\) is
the \(p\)-th partial derivative in \(t\) at \(t=0\) of the smooth map
\((Y,t)\mapsto\pi(g\exp Y\exp tX)v\) on \(\mathfrak g\times\mathbb R\). By
`contDiff_iteratedDeriv_snd`, that derivative is smooth in \(Y\).

## 2. Choosing the bounds and the smooth series

`exists_exponentialOrbit_bounds` takes \(\varepsilon\ge0\) and returns a sequence \(M\). It
bounds \(\|F^{(p)}\|\) on \([0,\varepsilon]\) by \(M_p\). For every real sequence \(c\) with
\(\sum_p|c_p|M_p<\infty\), the series \(w=\sum_p c_p u_p\) converges and \(w\) is a smooth
vector.

The construction cuts off in the identity chart. Let \(\beta\) be a smooth bump on \(\mathfrak g\)
equal to \(1\) on the unit ball, and put \(\Phi_p(Y)=\beta(Y)\,\pi(\exp Y)u_p\). These functions
are smooth and compactly supported, so every derivative of order \(k\) has a uniform bound
\(C_{p,k}\). Let \(B_p\) bound \(\|F^{(p)}\|\) on \([0,\varepsilon]\), and put
\[
M_p=B_p+\sum_{k\le p}C_{p,k}.
\]
This diagonal choice makes \(\sum_p|c_p|\,C_{p,k}\) converge for every fixed order \(k\). By
`contDiff_tsum`, the function \(Y\mapsto\sum_p c_p\Phi_p(Y)\) is therefore smooth. On the unit ball,
\(\pi(g\exp Y)w=\pi(g)\sum_p c_p\Phi_p(Y)\). So the orbit of \(w\) is smooth near every \(g\),
which is the criterion `IsExpLieAlgebra.contMDiffAt_iff_expG`.

## 3. The one-parameter factorization

`exists_eq_two_exponentialAverages` gives a smooth vector \(w\) and smooth scalar functions
\(a,b\), both supported in \([0,\varepsilon]\), with
\[
v=\int a(t)\,\pi(\exp tX)w\,dt+\int b(t)\,\pi(\exp tX)v\,dt .
\]
Take \(M\) from step 2. The one-variable lemma
`Langlands.Analysis.DixmierMalliavin.exists_dirac_eq_tsum_iteratedDeriv_add` gives
coefficients \(c\) with \(\sum|c_p|M_p<\infty\) and kernels \(a,b\) supported in
\([0,\varepsilon]\). For every smooth \(f\) whose derivatives are bounded by \(M\) on
\([0,\varepsilon]\) it gives
\[
f(0)=\sum_p c_p\int f^{(p)}a+\int f\,b .
\]
Put \(w=\sum_p c_p u_p\).

Fix a continuous linear functional \(L\) with \(\|L\|\le1\), and apply the identity to
\(f=L\circ F\). The bound \(|L(F^{(p)}(t))|\le M_p\) on \([0,\varepsilon]\) dominates the series
by \((|c_p|M_p)\,|a(t)|\). So the series and the integral can be interchanged
(`integral_tsum_of_summable_integral_norm`). By step 1,
\(\sum_p c_pL(F^{(p)}(t))=L(\pi(\exp tX)w)\). Thus both sides of the displayed vector identity
have the same value under every such \(L\). The Hahn–Banach theorem (`exists_dual_vector''`, in
`eq_of_dual_unitBall`) then gives equality in \(E\).

## 4. Iteration along a basis

For a functional \(L\) and a vector \(u\), let \(c_{L,u}(x)=L(\pi(x^{-1})u)\)
(`inverseCoefficient`). It is continuous because the action is jointly continuous. Step 3,
applied to \(-X\) and composed with \(L\circ\pi(x^{-1})\), gives
`exists_eq_two_coefficientAverages`:
\[
c_{L,v}(x)=\int a(t)\,c_{L,w}(\exp(tX)\,x)\,dt+\int b(t)\,c_{L,v}(\exp(tX)\,x)\,dt
\]
for all \(L\) and \(x\). The kernels and \(w\) do not depend on \(L\) or \(x\). The lemma records
the supports of \(a\) and \(b\) in \([-\varepsilon,\varepsilon]\), which contains the interval
\([0,\varepsilon]\) of step 3.

`exists_eq_sum_inverseCoefficients` proceeds by induction on the length \(d\) of a list
\(X_0,\dots,X_{d-1}\) in \(\mathfrak g\). It produces finitely many smooth vectors \(w_i\) and
smooth kernels \(K_i\) on \(\mathbb R^d\), supported in the closed sup-norm ball of radius
\(\varepsilon\), that is in the cube \([-\varepsilon,\varepsilon]^d\), such that
\[
c_{L,v}(x)=\sum_i\int_{\mathbb R^d}K_i(t)\,c_{L,w_i}\bigl(\exp(t_{d-1}X_{d-1})\cdots\exp(t_0X_0)\,x\bigr)\,dt
\]
(the reversed product is `IsExpLieAlgebra.revProdExp`). The step from \(d\) to \(d+1\)
directions applies the one-parameter identity in the direction \(X_0\). It then applies the
induction hypothesis to the remaining \(d\) directions, once for \(w\) and once for \(v\), with
kernels \(K_i\) and \(K'_j\) on \(\mathbb R^d\). The new kernels on \(\mathbb R^{d+1}\) are
\(a(t_0)K_i(t_1,\dots,t_d)\) and \(b(t_0)K'_j(t_1,\dots,t_d)\), and the integrals are combined by
Fubini (`IsExpLieAlgebra.sum_integral_cons_kernel`). The new kernels are smooth by
`contDiff_cons_kernel`. Their supports stay in the cube of the same radius by
`tsupport_cons_kernel`: a point \(t\) of the support has \(|t_0|\le\varepsilon\), and its tail
\((t_1,\dots,t_d)\) lies in \([-\varepsilon,\varepsilon]^d\). So \(\max_j|t_j|\le\varepsilon\).
This is where the sup norm is needed: with the Euclidean norm, these two bounds would only give
\(\|t\|\le\sqrt2\,\varepsilon\). Both kernel lemmas are in
`Langlands.Analysis.DixmierMalliavin.IteratedKernel`.

## 5. Haar density in coordinates of the second kind

`smoothVectorFactorization_exponentialCharts` proves the theorem for \(G\le A^\times\) with the
exponential charts. Take a basis \(b\) of \(\mathfrak g\). By
`IsExpLieAlgebra.exists_smooth_density_prodExp`, there is \(\varepsilon_0>0\) with the following
property. Every smooth \(K\) on \(\mathbb R^d\) supported in the closed sup-norm ball of radius
\(\delta\le\varepsilon_0\), the cube \([-\delta,\delta]^d\), comes from a smooth compactly
supported \(k\) on \(G\). This \(k\) is supported in the image of that cube under
\(P(t)=\exp(t_0b_0)\cdots\exp(t_{d-1}b_{d-1})\) (`prodExp`). It satisfies
\(\int_G k\varphi\,d\mu=\int K(t)\varphi(P(t))\,dt\) for every continuous \(\varphi\).

By the continuity of \(P\) and \(P(0)=1\), there is \(\varepsilon_1>0\) such that \(P\) maps the
cube \([-\varepsilon_1,\varepsilon_1]^d\) into \(U\). Put
\(\varepsilon=\min(\varepsilon_0,\varepsilon_1)\). Apply step 4 to the basis \(b\) at
\(x=1\), with this \(\varepsilon\). This gives
\(L(v)=\sum_i\int K_i(t)\,L(\pi(\mathrm{rev}(t)^{-1})w_i)\,dt\), where \(\mathrm{rev}\) is the
reversed product. Since \(\mathrm{rev}(t)^{-1}=P(-t)\) (`IsExpLieAlgebra.revProdExp_inv`) and
Lebesgue measure is invariant under \(t\mapsto-t\), this equals
\(\sum_i\int K_i(-t)\,L(\pi(P(t))w_i)\,dt\). The reflected kernels \(t\mapsto K_i(-t)\) are
still supported in \([-\varepsilon,\varepsilon]^d\), because \(\|-t\|=\|t\|\).

The density lemma, applied to the kernels \(t\mapsto K_i(-t)\) and to
\(\varphi(g)=L(\pi(g)w_i)\), turns this into \(\sum_i\int_G k_i(g)\,L(\pi(g)w_i)\,d\mu(g)\). Each
\(k_i\) is supported in \(P([-\varepsilon,\varepsilon]^d)\subseteq
P([-\varepsilon_1,\varepsilon_1]^d)\subseteq U\). The map
\(g\mapsto k_i(g)\,\pi(g)w_i\) is continuous with compact support, hence integrable. Continuous
linear maps commute with the Bochner integral, and Hahn–Banach again gives the identity in
\(E\).

## 6. Transport through the closed linear realization

`smoothVectorFactorization` takes the closed linear realization \(j\) and its image
\(K=j(G)\). By `IsClosedLinearRealization.isExpLieAlgebra`, \(K\) has the exponential Lie
algebra `lieSubmodule`. Moreover `IsClosedLinearRealization.rangeEquiv` is an isomorphism
\(e:G\to K\) of topological groups. Then \(\pi'=\pi\circ e^{-1}\) is a jointly continuous
representation of \(K\), and \(e_*\mu\) is a left Haar measure on \(K\) with the Borel structure.
Smoothness of maps out of \(G\) and out of \(K\) correspond under
`IsClosedLinearRealization.contMDiff_iff_comp_symm`. So \(v\) is smooth for \(\pi'\). Step 5
applies to the neighbourhood \(e(U)=\{z\in K\mid e^{-1}(z)\in U\}\) of \(1\) in \(K\), written
`e.symm ⁻¹' U` in Lean; it is a neighbourhood because \(e^{-1}\) is continuous. Step 5 gives
kernels \(k_i\) on \(K\) with support in \(e(U)\). The kernels \(k_i\circ e\) on \(G\) are smooth
and compactly supported. The support of \(k_i\circ e\) is the preimage under \(e\) of the support
of \(k_i\), and the preimage of \(e(U)\) under \(e\) is \(U\). The vectors \(w_i\) are smooth
for \(\pi\). The integrals and their integrability transfer by `integral_map_equiv` and
`integrable_map_equiv`.

## Correspondence with Dixmier–Malliavin

This is the complex Banach, closed linear case of J. Dixmier and P. Malliavin, *Factorisations
de fonctions et de vecteurs indéfiniment différentiables*, Bull. Sci. Math. (2) 102 (1978),
Theorem 3.3 and its proof (retained English translation, PDF pp. 8–9). Theorem 3.3 treats a
continuous representation of a Lie group on a Fréchet space, and its proof follows the
proof of Theorem 3.1.

- Steps 2–3 are the paragraph of the proof of Theorem 3.3 on the first basis vector, with the
  scalar identity of Lemma 2.5(3) and Remark 2.6 (PDF pp. 5–6). Dixmier and Malliavin use the
  even powers \(x_1^{2n}\) and supports in \([-\varepsilon,\varepsilon]\). Their summability
  comes from the bounds \(M_{nij}=p_j(\pi(u_i)\pi(x_1)^{n}\xi)\), where the \(p_j\) are
  seminorms of the Fréchet space and \((u_i)\) is a basis of the enveloping algebra. The Lean proof uses the Library's one-variable lemma instead, which has
  all derivatives and supports in \([0,\varepsilon]\). It controls the smoothness of the limit
  \(w\) through the chart bounds \(C_{p,k}\) of step 2, not through the enveloping algebra. It
  proves the identity \(\pi(\mu)\eta=\xi+\pi(\nu)\xi\) by testing against continuous functionals,
  where the source passes to a weak limit.
- Steps 4–5 are the inductive argument of Theorem 3.1(2)–(3), using the coordinates of the
  second kind of Theorem 3.1(1) and the smooth density of Haar measure in them (PDF pp. 6–7).
  The source multiplies one-parameter measures on the left of a convolution. The Lean proof
  iterates the identity for the coefficient \(x\mapsto L(\pi(x^{-1})v)\) instead, so its
  kernels sit in front of the reversed product. The inversion and the sign change at the end of
  step 5 return them to the ordered product \(P\). The product kernels are supported in the cube
  \([-\varepsilon,\varepsilon]^d\), as in Theorem 3.1(3), where the source takes the product
  \(f_1(t_1)\cdots f_m(t_m)\) with support in \([-\varepsilon,\varepsilon]^m\).
- Step 6 is not in the source, which works on an abstract Lie group. Here the closed linear
  realization supplies the exponential charts, and the kernels and averages are those of the
  original group \(G\) and representation \(\pi\).
