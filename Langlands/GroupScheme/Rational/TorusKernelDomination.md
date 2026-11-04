# Kernel parametrizations for torus quotients

This internal construction specializes the actual kernel-difference map to
a pointed torus parametrization `p : D → H` and a group homomorphism
`q : H → Q` with torus target. Every field and characteristic is retained.
The source torus and target torus can both be nonsplit.

`quotientHom` uses published pointed-morphism rigidity for arbitrary tori
to construct the group homomorphism `φ : D → Q` with underlying scheme map
`q ∘ p`. It retains that underlying map exactly. `parametrization` is the
actual scheme morphism `D × ker(φ) → ker(q)` of `KernelDomination`, sending
`(d,k)` to `p(d)⁻¹p(dk)`. Its identity-pair formula is also retained.

`parametrization_isDominant` assumes `H` smooth and affine over the field,
`p` dominant and pointed, and `q` dominant. It supplies both flatness
hypotheses needed by the published kernel-difference result: a dominant
homomorphism of finite-type affine groups onto a torus is flat by
`DominantHomFlat.flat_of_isDominant`. Torus smoothness gives reducedness
and local noetherianity of `Q`; source finite type and affineness give local
finite type and quasi-compactness of the homomorphisms. The composite
`q ∘ p` is dominant. Smoothness of `H` makes `p` schematically dominant,
and affineness gives its quasi-compactness and that of `H` over the field.
The actual kernel parametrization is therefore topologically dominant.
No flatness assumption on either quotient map is left to the caller.

`isSplitTorus_quotient` additionally takes `D` split and concludes that
`Q` is split. It needs neither smoothness nor affineness of `H`: the
pointed composite is dominant between the split torus `D` and torus `Q`,
so the published split-domination theorem applies directly.

The provenance is internal, from the published pointed torus homomorphism
constructor, kernel-difference construction, torus geometry, smooth
reducedness and dominant-homomorphism flatness. The actual kernel of
`φ` can remain disconnected or nonsmooth; this contribution does not
replace it by a torus or conclude unipotent splitness or maximal-torus
conjugacy.
