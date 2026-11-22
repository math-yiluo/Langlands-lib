# Chamber bound for the deviation from a maximal-parabolic constant term

`AdelicMaximalUnipotentOscillationStatement` concerns a connected reductive group \(G\) over a number field \(F\), a maximal split torus \(T\), and a generic cocharacter specifying simple relative roots \(\Delta\). For \(\alpha\in\Delta\), use an affine smooth connected unipotent group \(U\) embedded as the closed model of the standard radical for \(\Delta\setminus\{\alpha\}\). The statement uses specified smooth relative dimensions for \(G\) and \(U\), and a torus morphism \(T_0\to T\). Write \(a_G\) for the image of an intrinsic positive point \(a\) of \(T_0\) in \(G(\mathbb A)\).

Fix a common positive threshold for the restricted simple-root norms, a compact set \(\Omega\) of left factors normalizing the image of \(U(\mathbb A)\), a compact set \(Y_f\) of finite coordinates, an open right finite level \(L\), and a compact set \(K\) of right factors. The theorem chooses a compact \(K'\supseteq K\) and a constant \(C\ge 0\). Take \(p\in\Omega\), \(a\) in the weak simple-root chamber, and \(k\in K\) with \((p a_G k)_f\in Y_f\). Let \(f\) be continuous, smooth on archimedean slices, left \(U(F)\)-invariant, and right \(L\)-invariant. If all the fixed basis right-orbit derivatives have norm at most \(M\ge 0\) at \(p a_G k'\) for \(k'\in K'\) with \(k'_f=k_f\), then

\[
  |f(p a_G k)-\operatorname{CT}_U f(p a_G k)|
  \le C\,|\alpha(a)|_{\mathbb A}^{-1/[F:\mathbb Q]} M.
\]

The constant term is the integral on the actual rational unipotent quotient with normalized probability Haar measure.

The proof chooses compact archimedean representatives on the prescribed finite slice. Conjugating their image by \(p^{-1}\) stays in a compact subset of the unipotent image, and conjugating by \(a_G^{-1}\) contracts the polynomial coordinates. These coordinates lie in a fixed compact ball, whose inverse coordinate image in the archimedean group enlarges the original right factors from \(K\) to \(K'\). The coordinate mean-value bound estimates the difference at each representative, and integration over the unipotent quotient gives the inequality.

This is a first-order form of the estimate used in Mœglin–Waldspurger, §I.2.10, pp. 30–33. It records the finite coordinate explicitly so that the estimate can be iterated on the same compact finite slice.
