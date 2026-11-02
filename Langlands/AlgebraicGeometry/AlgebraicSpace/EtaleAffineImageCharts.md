# Affine open image charts after an etale base change

This internal construction links the finite scheme charts and the affine image quotient helper. It works with an fppf sheaf `F`, an etale scheme chart `a : h_W → F`, and a monomorphism `f : F → h_Y`, retaining an arbitrary base universe `u`.

`EtaleAffineImageChart F a f x` records an affine scheme `T` and an etale morphism `T → Y`; an actual fppf sheaf with a cartesian square representing `F ×_{h_Y} h_T`; an affine source scheme `D`; an etale map `D → W`; a finite map `D → T`; and an etale chart `h_D → F ×_{h_Y} h_T` compatible with both projections. Its sheafified image is an affine open subfunctor. It also records a point of `D` mapping to the given point `x` of `W`. The image inclusion is the canonical inclusion of that subfunctor.

`nonempty_etaleAffineImageChart_of_finiteChart` constructs this data from `EtaleFiniteChart w.left x`, where the actual scheme composite `w : W → Y` satisfies `a ≫ f = h_w`. The finite chart's source and base get their induced structure morphisms to the original base. Its map into the scheme pullback `W ×_Y T` is etale. The pullback of `F` is formed in the category of fppf sheaves; forgetting to presheaves preserves its cartesian square. Cancellation of the bottom square from the outer scheme pullback square makes the induced map `h_{W ×_Y T} → F ×_{h_Y} h_T` a base change of `a`, hence etale. Composing gives the indicated etale chart. Its composite to `h_T` is finite and the projection to `h_T` is monomorphic, so `isAffineOpen_sheafify_range_of_finite_mono_composite` makes its image affine open.

`nonempty_etaleAffineImageChart` first constructs a finite chart using `nonempty_etaleFiniteChart`. It assumes that `w.left` is separated and locally of finite type and is quasi-finite at `x`. These are hypotheses of this local helper; no general schemehood statement is claimed.

Provenance is internal and derived from the finite-chart construction, affine image quotient theorem, Mathlib preservation of sheaf limits, and pullback pasting. No algebraic-space representability theorem is assumed.
