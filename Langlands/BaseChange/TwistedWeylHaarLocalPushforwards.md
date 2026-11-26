# Twisted local Haar pushforwards for Weyl integration on `GL_n`

The Lean theorem proves the local pushforward identities for the twisted
Weyl map on the regular semisimple norm image. The Haar measure on the
base-changed rational torus subgroup is transported from rational torus
Haar by base change. The left quotient measure is compatible with this
subgroup Haar measure and ambient Haar. The source is the product of the
quotient measure and rational torus Haar pulled back to the regular norm
domain, weighted by the residue-normalized absolute ordinary Weyl
discriminant evaluated at the norm.
[Henniart–Lemaire, II.2.4 and II.2.10, formula (1)](https://www.numdam.org/issues/MSMF_2011_2_124__1_0/)

The additive trace from the extended torus Lie algebra to the rational
torus Lie algebra sums the cyclic translates entrywise and identifies
the result with a rational matrix. For a trace-one coefficient \(c\) in
the cyclic algebra, sending a rational Lie vector \(X\) to \(c X_E\),
where \(X_E\) is its coefficient extension, gives a section of this
trace. The strict inverse function theorem along that direction gives
a local inverse of the norm near the identity. The norm homomorphism
then has open image. Choosing one translate of the local section on
each coset of an open subgroup supplies exact lifts with strictly
differentiable representatives throughout the regular norm domain.

Split the ambient matrix space into the rational torus direction and a
linear complement. Multiplication in a small compact open subgroup has
identity derivative in these coordinates, giving a transverse chart on
the quotient. If the ambient and rational torus charts have densities
\(c_G\) and \(c_T\) with respect to additive Haar, compatibility gives
the transverse chart density \(c_G/c_T\). Multiplying the transverse and
rational torus densities gives \(c_G\) before weighting. The discriminant
weight is constant on a smaller torus patch. Right translation moves the
quotient chart to the required coset. The corresponding twisted translation
and normalization at the chosen lift preserve ambient Haar.

The strict derivative on the transverse direction is the twisted
adjoint minus the identity. On the torus direction it is the trace
section obtained by differentiating the exact norm lift. Over an
algebraic closure the cyclic coordinates give the weighted cyclic
defect with a correction in the torus direction. The determinant reduces
to the ordinary Weyl discriminant by the weighted cyclic block calculation.
[Clozel, §6.3, Lemma 5](https://numdam.org/articles/10.24033/msmf.299/)

Reversing the sign of the transverse coordinate preserves its additive Haar measure.
The strictly differentiable ball chart therefore scales additive Haar by
the reciprocal absolute discriminant, canceling the weight and giving
the required exact pushforward onto its open image.
