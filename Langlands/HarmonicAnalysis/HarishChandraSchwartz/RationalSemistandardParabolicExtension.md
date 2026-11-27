# Extension of a semistandard parabolic from a literal Levi

Fix an ambient maximal split torus and a semistandard parabolic \(P=MU\). The
same torus lifts to the chosen model of \(M\), where it is again maximal split.
`RationalSemistandardParabolicLift.atInheritedTorus` takes a semistandard
\(P^M=M'U^M\) for that torus and constructs the corresponding ambient index
\(P'=M'(U^M U)\). Its parabolic is \(P^M U\). The final Levi is the image of
\(M'\), and the inverse image of the radical of \(P'\) under the inclusion of
\(M\) is \(U^M\). The products are statements on every test scheme.

On rational points, `innerLeviPointsEquiv` and `innerRadicalPointsEquiv`
restrict the point homeomorphism of the outer Levi model. They identify the
inner Levi and radical with their respective ambient subgroups intersected
with the literal outer Levi, using its induced topology. Both maps are given
by the actual Levi inclusion when evaluated in the ambient group.

The intrinsic dynamic coverage theorem presents both input indices by
cocharacters. `Dynamic.nestedRealization` realizes the extended parabolic
and radical and the image of the inner Levi simultaneously. The lifted torus
in the final Levi composes with the inclusion of \(M\) to the original
ambient torus, so the result is semistandard there. This construction gives
the parabolic and radical products used in the nested constant-term diagram
of III.6 and the index \(P'=P^M U\) used in the Fourier comparison of VIII.2.1.

[Waldspurger (2003), III.6, printed p. 272, and VIII.2.1, printed pp. 321–322](https://doi.org/10.1017/S1474748003000082)
