# Full tensor comparison for a product's top derivative

This supporting construction specializes the published all-rank general linear
Leibniz filtration to derivative order `a + b`. The only feasible pair of
factor derivative orders is `(a,b)`. A singleton filtration identifies the
source functor with its sole grade. `topProductIso` selects the resulting
natural isomorphism of representation-valued functors.

`topProductTensorEquiv` then gives a complex linear equivalence from the full
carrier of the product's top derivative to the full tensor product of the
factor top-derivative carriers. It composes the component of that natural
isomorphism, identity carrier transport along the grade's rank equality, and
the published `binaryZeroZeroTensorEquiv`. This last map removes the universe
lift from the rank-zero binary product and retains the entire tensor carrier.

The parameters are an arbitrary prime, a p-adic field in universe `uF`, its
supplied topological data, a continuous nontrivial unitary additive character,
and arbitrary smooth complex factors with independent carrier universe `uV`.
Both ranks may be zero. The source carrier is in `max uF uV`; the tensor target
is in `uV`. No irreducibility, admissibility, finite length, or dimension premise
is imposed. No preferred choice of the natural isomorphism is asserted.

`topProductTensorEquiv_naturality` proves that applying the comparison after
the top derivative of the binary product map equals applying the tensor product
of the two top-derivative maps after the comparison. The proof evaluates the
naturality square of `topProductIso`, removes the identity carrier rank
transport, and applies the published naturality of
`binaryZeroZeroTensorEquiv`. Both factor maps are arbitrary.

The provenance is derived: the mathematical input is the proved and published
`generalLinearDerivativeLeibnizFiltration`, together with elementary quotient
and rank-zero tensor constructions. BZ77 Corollary 4.14(c), printed p.458,
is the original context for the filtration. This construction asserts no
individual segment derivative formula or special-head product irreducibility
criterion; those host obligations remain open.

The original context is Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
printed p.458 / PDF p.19, Corollary 4.14(c). The arbitrary-carrier rank-zero
extension uses the Library's binary tensor product definition. The new
isomorphisms are derived formal constructions, rather than a separately assumed
source theorem.

The import inventory against Library
`a5dff2ff93bd3637a67ee8847f67f811efc82f01` has 325 project modules, including
the two new modules, and 130 external import roots. Every inherited Lean and
Markdown pair matches that Library. The inherited closure is the same as the
previously inspected general Leibniz proof; the only addition is the elementary
singleton extraction. Its inherited classification modules are
`Supercuspidal`, `SupercuspidalContragredientAux`, and
`SupercuspidalContragredientStatement`. Exact excluded-declaration scans find
no hit, and the new construction invokes only the published general Leibniz
theorem, natural quotient first isomorphism, rank transport, and binary
rank-zero tensor equivalence. It uses no Zelevinsky 1980 segment derivative
formula, segment-socle assertion, head criterion, or downstream classification.
The inventory and inherited byte comparison are dependency checks, not a claim
to have reread all 325 module bodies.
