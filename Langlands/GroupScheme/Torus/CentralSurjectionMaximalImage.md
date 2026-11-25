# Maximality of supplied torus images under central fppf surjections

`Langlands.GroupScheme.RelativeCentralSurjectionMaximalImageStatement.{u}` is the named `Prop`-valued statement recording
maximality on residue fibres of a supplied relative-torus image under a central fppf homomorphism of reductive groups.
`Langlands.GroupScheme.relativeCentralSurjectionMaximalImage` proves this proposition by the existing helper theorem.
The helper signatures and all mathematical hypotheses are retained; the
other results below are proved companion helpers.

This internal helper extends the published
`centralSurjectionMaximalSplitTorusImage` theorem from split tori to arbitrary
field tori, and then to residue-field maximality over an arbitrary scheme.
It supplies the maximality step in the forward torus correspondence of
Conrad, *Reductive group schemes* (2014), Corollary 3.3.5 and Exercise
5.5.9(i), registered as `conrad-2014-reductive-group-schemes`.

`IsMaximalTorus.image_of_centralFppfHom` considers a central fppf homomorphism
between connected reductive groups over a field, a maximal source torus,
and a supplied closed target torus. An fppf map of these tori must form a
commuting square with the ambient homomorphism. The target torus is then
maximal among all closed tori. The kernel of the ambient homomorphism
need not be finite or smooth.

The proof extends the field to its algebraic closure. Finite Galois splitting
makes every torus there split. Field-extension preservation of maximality
turns the source torus into a maximal split torus, so the published
split-image theorem applies. Since every torus over the algebraic closure
is split, this gives full maximality. Field-extension reflection then
recovers maximality over the original field.

`IsFibrewiseMaximalTorus.image_of_centralFppfHom` applies the field theorem
to every actual residue-field fibre of the base. Reductivity, the fppf
conditions, closedness, the commuting square, and centrality of the actual
kernel all survive this base change. The target torus is assumed to be
a relative torus. Its construction and the construction of the fppf torus
map are separate obligations.
