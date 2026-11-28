# The quadratic first twist for a split cover

`Langlands.Covering.Dual.FirstTwistData A L` packages the algebraic inputs to
the first twist. The base `A` is a commutative group, `L` is a `ℤ`-module,
`Q` is a `QuadraticForm ℤ L`, and `M` is a submodule. The degree `n` is
positive and divides the polarization \(B_Q(x,y)\) for all \(x,y \in L\)
and the values \(Q(m)\) for \(m \in M\). The bimultiplicative pairing
\(h\) takes values in \(\mathbb C^\times\) with \(h(a,b)^n=1\).

For `D : FirstTwistData A L`, `D.Character` is the pointwise
multiplicative group of complex-valued characters on the additive
quotient `L ⧸ D.M`, expressed as `Multiplicative (L ⧸ D.M) →* ℂˣ`.
The formula
\[
  c_1(a,b)([y]) = h(a,b)^{Q(y)}
\]
first defines an additive homomorphism from \(L\) to the additive copy of
\(\mathbb C^\times\). Indeed, the factor
\(h(a,b)^{B_Q(x,y)}\) from expanding \(Q(x+y)\) is one. The divisibility
condition on \(Q|_M\) makes this homomorphism descend through the quotient.
`D.c₁` is bundled as a homomorphism in each variable using the pairing
laws, and `D.c₁_apply_mk` gives the displayed formula on every class.

The diagonal identity \(B_Q(y,y)=2Q(y)\) yields `D.c₁_sq`. When \(n\) is
odd, its coprimality with \(2\) gives \(n\mid Q(y)\) for all \(y\), hence
`D.c₁_eq_one_of_odd`. Bimultiplicativity gives the normalized
two-cocycle `D.cocycle` for the trivial action, with the same evaluation
in `D.cocycle_apply_mk`. If \(h(b,a)=h(a,b)^{-1}\), then exchanging \(a\)
and \(b\) inverts the character. Its square is one, so the cocycle is
symmetric by `D.cocycle_symm`.

`D.Extension` uses the [normalized cocycle extension](../../GroupTheory/CocycleExtension.md).
Its multiplication on coordinates is
\[
  (\chi,a)(\psi,b)=(\chi\psi c_1(a,b),ab).
\]
`D.inclusion` is the injective map \(\chi\mapsto(\chi,1)\) with central
image, and `D.projection` is the surjection \((\chi,a)\mapsto a\) with
kernel equal to that image. `D.sectionMap` sends \(a\) to \((1,a)\).
`D.sectionMap_mul` expresses its multiplicative defect as the inclusion
of \(c_1(a,b)\). Under the skew relation on \(h\),
`D.extensionCommGroup` makes the extension commutative.

Gan and Gao, *The Langlands–Weissman Program for Brylinski–Deligne
Extensions*, Astérisque **398** (2018), §5.2, printed pp. 213–214
(one-based PDF pp. 231–232), give the formula and the order-two and
odd-degree consequences for the modified cocharacter lattice
\(L=Y_{Q,n}\), the modified coroot lattice \(M=Y_{Q,n}^{\mathrm{sc}}\),
and the Hilbert symbol. The module uses their algebraic divisibility
and pairing conditions with these inputs supplied abstractly.
The registered source is `gan-gao-2018-langlands-weissman-program`,
SHA-256 `fabbe056bdec2a5d57a22a0d3ad275640d0343c3f71092a7df427f7ebaebe892`.
