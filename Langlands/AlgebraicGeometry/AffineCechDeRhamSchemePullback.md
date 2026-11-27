# Čech–de Rham pullback along a morphism of schemes

For a morphism \(\gamma\colon X\to Y\) over \(\operatorname{Spec} R\), take
affine covers and an index map \(\beta\) such that each source chart maps
into its assigned target chart, \(U_i\subseteq\gamma^{-1}V_{\beta(i)}\).
For opens \(W\subseteq\gamma^{-1}Z\), `pullbackSections` is the actual
morphism's map on sections \(\Gamma(Y,Z)\to\Gamma(X,W)\). The base
equation makes it an \(R\)-algebra homomorphism.

`LocalPullbacks.ofMorphism` uses these maps on every tuple intersection,
for every ideal \(I\) and every selected vertex. Their compatibility with
the face restrictions uses `Scheme.Hom.appLE_map` and
`Scheme.Hom.map_appLE`. Every vertex of an intersection supplies the same
map, so their differences are zero and lie in every extended ideal.

For smooth separated schemes and finite covers, `schemePullbackH1` is
the map `LocalPullbacks.pullbackH1` of this system for the zero ideal.
The difference contractions vanish. The function component of an input
with zero function component therefore remains zero, and a compatible
closed one-form pulls back to a compatible closed one-form.
`schemePullbackH1_maps_hodgeF1` states that `hodgeF1` maps into
`hodgeF1`.

The construction uses pullback of relative forms and the explicit affine
Čech differential in Kai-Wen Lan, *Arithmetic compactifications of
PEL-type Shimura varieties*, revised 14 March 2021, §2.1.6, printed
pp. 129–135. The retained source is `lan-2008-pel-thesis-revision-2021`,
SHA-256 `a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
