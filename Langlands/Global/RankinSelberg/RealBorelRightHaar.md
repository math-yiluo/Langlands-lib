# Right Haar measure on the real upper triangular group

For each rank \(r+1\), `rightBorelMeasure r` is the image of the product of
multiplicative Haar on the diagonal torus and the upper-entry Haar measure at
additive parameter \(1\). The coordinate homeomorphism sends \((d,u)\) to
\(u\operatorname{diag}(d)\). The product measure is finite on compact sets and
positive on nonempty open sets, so its image has both properties as well.

Right translation by \(u_0\operatorname{diag}(d_0)\) sends the torus coordinate
\(d\) to \(dd_0\). It sends \(u\) to the right translate by
\(\operatorname{diag}(d)u_0\operatorname{diag}(d)^{-1}\). The torus is abelian,
and the upper-entry measure has right invariance. The measure-preserving skew
product lemma therefore applies. Left translation by an upper unipotent fixes the
torus coordinate and is ordinary left translation of the second coordinate.

`RealBorelRightHaarStatement` collects these properties. This is an internal
measure construction for averaging smooth tests along the real upper triangular
group in the proof of Whittaker uniqueness.
