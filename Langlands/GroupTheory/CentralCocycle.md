# Normalized two-cocycles for central extensions

`Langlands.CentralTwoCocycle G A` uses `Langlands.NormalizedTwoCocycle` with the trivial action of the group \(G\) on the commutative group \(A\). This action restricts the tautological action of `MulAut A` along the constant identity homomorphism. In these coordinates the cocycle equation is

\[
\sigma(gh,j)\sigma(g,h)=\sigma(h,j)\sigma(g,hj).
\]

The constructions follow directly from this equation and normalization at \((1,1)\). `pullback` substitutes group homomorphism values for the three variables. `map` applies a coefficient homomorphism to the equation. `pointwiseMul` groups the factors for each cocycle using commutativity of \(A\). `ofBilinear` expands both sides using multiplicativity in each variable.

The extension has the inclusion, projection and exactness of `Langlands.NormalizedTwoCocycle.Extension`. The lemma `inl_mem_center` applies its multiplication rule with an included coefficient and reduces the action to the identity.
