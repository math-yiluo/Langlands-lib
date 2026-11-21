# Positive torus points killed by simple roots lie in the split component

Source: Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series* (2024), §7.2, pp. 211–212 (arXiv TeX lines 1966–1972). There BL fix \(a_\alpha\in\mathfrak A^G_{P_\alpha}\) for each simple root \(\alpha\), "in particular \(a_\alpha\) lies in the center of the Levi part of \(P_\alpha\)", and \(z_j\in\mathfrak A_G\). The published `IsLocalFinitenessGroupData` (module `AdelicLocalFinitenessStatement`) does not quantify over \(\mathfrak A_{P_\alpha}\) directly. It describes these points as images \(\iota_T(t_\alpha)\), \(\iota_T(z_j)\) of points of the positive real torus \(\mathfrak A_T\) of the maximal split torus: every simple root other than \(\alpha\) is \(1\) on \(t_\alpha\), and every simple root is \(1\) on \(z_j\). This module **states** the comparison of the two descriptions, in the direction from torus conditions to split-component points. It does not prove it.

## The statement

`PositiveTorusSplitComponentStatement` quantifies over a number field \(F\), an affine group scheme \(G\) of finite type, a `StandardParabolicFamily` \(\mathcal F\) (maximal split torus \(\iota:T\to G\), generic cocharacter, and the actual standard parabolics \(P_J\) with Levi \(M_J\) and specified split component \(A_J\)), a standard index \(J\), and a point \(t\in T(\mathbb A)\). Assume:

- \(t\in\) `PositiveRealTorus.intrinsicSubgroup F 𝓕.T`, i.e. every character of \(T\) takes a positive real scalar idele value at \(t\);
- \(\beta(t)=1\) (`Lie.characterValue β t = 1`) for every simple root \(\beta\in J\).

Then there is \(a\in\) `𝓕.positiveSplitComponent J`, the image in \(P_J(\mathbb A)\) of the positive real points of \(A_J\), whose image in \(G(\mathbb A)\) is \(\iota(t)\).

For \(J=\Delta_0\setminus\{\alpha\}\) this gives \(\iota_T(t_\alpha)\in\mathfrak A_{P_\alpha}\), and for \(J=\Delta_0\) it gives \(\iota_T(z_j)\in\mathfrak A_G\). These are the hypotheses `hx` of the theorems of `AdelicLocalFinitenessProductBridge`, which turn the product step of BL Lemma 8.1 into equations of \(\Xi_{\mathrm{main}}\).

## Why it is true (not formalized here)

\(A_J\) is the maximal split central torus of the standard Levi \(M_J\). Through the specified map \(f_J:A_J\to T\) (`factor_comp`: \(f_J\circ\iota=\) the composite \(A_J\to M_J\to P_J\to G\)) it is the identity component of \(\bigcap_{\beta\in J}\ker\beta\). Hence restriction \(X^*(T)\to X^*(A_J)\) is surjective, with kernel the characters having a nonzero multiple in \(\mathbb ZJ\). A positive point of \(T\) is a homomorphism \(X^*(T)\to\mathbb R_{>0}\). If it kills \(J\) it kills that kernel, because \(\mathbb R_{>0}\) is torsion-free. So it factors through \(X^*(A_J)\) and defines a positive point \(a'\) of \(A_J\) with \(f_J(a')=t\). Then \(a\) is the image of \(a'\) in \(P_J(\mathbb A)\). The analytic structure of the positive torus enters only through characters; the identification of \(f_J(A_J)\) with the connected kernel is the algebraic-group input.

## Scope

The converse direction (that a positive split-component point satisfies the torus conditions and the normalization \(H_G=0\) of `IsLocalFinitenessGroupData`) is not stated. The statement keeps the exact interfaces of `StandardParabolicFamily`, `PositiveRealTorus.intrinsicSubgroup` and `AdelicGroupPoints.map`.
