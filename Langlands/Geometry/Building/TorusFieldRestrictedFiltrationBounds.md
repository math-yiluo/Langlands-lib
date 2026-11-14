# Algebraic bounds under torus and ground-field restriction

This is an internal consequence of the existing exact torus-then-field filtration
formula, boundedness of finite ordered products of upper root filtrations, and
cofinal descent of regular-function bounds. It claims no new literature result.

`TorusFieldRestrictedRootFiltrationBoundedStatement` quantifies over fields `k`
and `K` in any universe, an algebra structure, their supplied compatible valuative
relations, and a valuatively cofinal extension. The ambient group over `k` is
smooth, affine and locally of finite type. A split torus `S` over `k` maps into
this group. A split torus `T` over `K` maps monomorphically into the actual
base-changed group, with opposite factor pairs and an actual root-datum valuation.
The homomorphism from the base change of `S` to `T` factors the original inclusion.
If every upper relative-root filtration is algebraically bounded at every real
depth, every original relative-root filtration of the canonical torus-then-field
restricted family is algebraically bounded at every real depth, in the original
group for its prescribed valuative relation.

The proof uses the published exact preimage equality. The original root remains
a nonzero root after base change. The upper torus-restricted subgroup is a finite
ordered product of actual upper-root filtrations at positive integer multiples
of the chosen depth; the assumed all-depth bounds therefore bound that whole
subgroup. Cofinality then descends bounds on every actual regular function from
its rational-extension preimage to the original field. The resulting restricted
filtration has the same real depth.

Upper-family boundedness is an explicit premise. This result constructs neither
a quasi-split apartment nor a proof of the unconditional maximal-unramified
boundedness target.
