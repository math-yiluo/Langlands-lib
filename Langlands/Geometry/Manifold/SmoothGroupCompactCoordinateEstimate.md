# Invariant derivative estimate on a compact coordinate ball

`SmoothGroupCompactCoordinateEstimateStatement` takes a smooth map \(\psi\colon E\to G\) from a finite-dimensional real normed space into a smooth Lie group with a finite-dimensional real model space. Fix a closed ball \(S\) about zero in \(E\) and a compact subset \(K\subseteq G\).

For \(k\in K\), \(x\in G\), and a smooth complex-valued \(f\), suppose that every right-orbit derivative in the fixed basis of the model space has norm at most \(M\) at \(x\psi(z)k\) for all \(z\in S\). Then for \(v\in S\),

\[
  |f(x\psi(v)k)-f(x\psi(0)k)|\le C\|v\|M ,
\]

with \(C\) independent of \(x,k,v,f,M\). The right-orbit derivative in a direction \(X\) differentiates \(t\mapsto f(gt)\) at \(t=1\).

The proof computes the coordinate derivative by factoring through \(y\mapsto k^{-1}\psi(z)^{-1}\psi(y)k\). The differential in \(y\) at \(z\) therefore lands in the tangent space at the identity. It depends continuously on \((k,z)\), so its operator norm is bounded on the compact product \(K\times S\). A fixed basis bounds the operator norm of the right-orbit differential from the individual derivatives. The mean-value inequality on \(S\) gives the result.

This estimate provides the passage from coordinate contraction to derivative bounds in the decay argument of Mœglin–Waldspurger, §I.2.10, pp. 30–33.
