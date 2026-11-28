# The lattice sign-cocycle extension

Let \(Y\) be an additive abelian group, \(D\) an integral bilinear form on
\(Y\), and \(F\) a field. The function \(c(y,z)=(-1)^{D(y,z)}\) takes values
in \(F^\times\). Bilinearity and the integer power law give the cocycle
identity for the trivial action, and \(D(0,0)=0\) gives normalization.
`latticeSignCocycle` packages these facts in `Langlands.NormalizedTwoCocycle`.
The construction uses only the additive group of the lattice, so the Lean
definitions apply without a freeness or finite-rank hypothesis on \(Y\).

`LatticeSignExtension` uses the group of the normalized cocycle. In the
coordinates supplied by `LatticeSignExtension.mk`, its multiplication is
\[
(y,a)(z,b)=(y+z,ab(-1)^{D(y,z)}).
\]
`LatticeSignExtension.groupExtension` packages the original cocycle
inclusion and projection in Mathlib's `GroupExtension`. The trivial
action makes the coefficient group central.

For the commutator convention \([x,x']=xx'x^{-1}x'^{-1}\), let \(y\) and \(z\)
be the respective projections of \(x\) and \(x'\). The proof of
`LatticeSignExtension.commutator` uses the product law in both orders.
Multiplying \(x'x\) by the central unit \((-1)^{D(y,z)+D(z,y)}\) gives
\(xx'\), since the sign with exponent \(2D(z,y)\) is \(1\). Right
cancellation gives the stated image of that unit. All arguments apply in
characteristic two, where the sign unit is \(1\).

Brylinski–Deligne, *Central extensions of reductive groups by \(K_2\)*,
Proposition 3.11 and its proof, formula (3.11.1), printed pp. 31–32
(PDF pp. 27–28), give the sign cocycle and commutator for the bilinear
form representing a quadratic form. Registered source
`brylinski-deligne-2001-central-extensions`, SHA-256
`24ea359c677a6c767a5eeeffad7d39f7019d875d3f18c5280f5086414e182ba5`.
Gan–Gao, *The Langlands–Weissman program for Brylinski–Deligne
extensions*, §2.6, printed p. 200 (PDF p. 218), gives the group law
in these coordinates. Registered source
`gan-gao-2018-langlands-weissman-program`, SHA-256
`fabbe056bdec2a5d57a22a0d3ad275640d0343c3f71092a7df427f7ebaebe892`.
