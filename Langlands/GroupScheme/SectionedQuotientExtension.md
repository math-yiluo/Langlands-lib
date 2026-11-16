# Quotienting a sectioned extension without changing its kernel

This module gives an internal construction over an arbitrary scheme `S`, in
every universe. All groups and homomorphisms below are group schemes over `S`.
Its provenance is a derivation from the Library's fppf homomorphism descent,
all-test subgroup functors, representability comparison, and descent of flatness
and local finite presentation. It does not translate a separate cited statement.

Supply homomorphisms `p : B → T`, `t : T → B`, and `z : Z → T`, with
`t ≫ p = id`, and fppf quotients `qB : B → P` and `qT : T → D` whose full
kernels are `range (z ≫ t)` and `range z`. Here the Library predicate
`RelativeRoot.IsFppfQuotient F q` means that the underlying scheme map is flat,
surjective, and locally of finite presentation, and that the full range of its
actual kernel inclusion equals `F`. All range and kernel identities quantify
over every relative test scheme, including non-affine tests.

The definition `hom` constructs `r : P → D`. The theorem `fac` proves
`qB ≫ r = p ≫ qT`, and `unique` proves that this equation uniquely determines
`r`. These three results do not require `p` to be an fppf quotient.

For the remaining results, also supply a homomorphism `i : U → B` whose
underlying morphism in `Over S` is monic, and assume that `p` is an fppf quotient
with full kernel `range i`. Then:

- `inclusion_point_eq_one` proves that a point of `U` killed by `i ≫ qB` is
  the identity, on every relative test.
- `inclusion_mono` proves that the underlying morphism of `i ≫ qB` in `Over S`
  is monic.
- `kernel_eq` identifies `range (kernelι r)` with `range (i ≫ qB)`.
- `isFppfQuotient` proves that `r` is flat, surjective, and locally of finite
  presentation, with that full kernel.
- `inclusion_isClosedSubgroup` proves that `i ≫ qB` is a closed subgroup
  inclusion if the structure map of `D` is separated.

The kernel group in these conclusions is the original `U`. No replacement or
quotient of `U` is introduced.

The construction first proves `kills_kernel`. A point of the actual kernel of
`qB` factors through `z ≫ t`. Applying `p ≫ qT` reduces, by the section
identity, to applying `z ≫ qT`, which is the identity point by the supplied
kernel equality for `qT`. The Library's `FppfHomDescent.hom` then descends
`p ≫ qT` through `qB`; its factorization and uniqueness theorems give `fac`
and `unique`.

For monicity, suppose `x` is a point of `U` killed by `i ≫ qB`. Exactness for
`qB` expresses `x ≫ i` as `y ≫ z ≫ t`. Apply `p`: the left side becomes
the identity by exactness for `p`, and the right side becomes `y ≫ z` by the
section identity. Hence `x ≫ i` is the identity; monicity of `i` gives the same
for `x`. Applying this argument to `x⁻¹ * y` proves cancellation for arbitrary
test points and hence `inclusion_mono`.

For the forward kernel inclusion of `kernel_eq`, pull back `qB` along a point
`x` of `P` killed by `r`. The resulting map of relative test schemes is fppf
and supplies a lift `b` to `B`. The equation `qB ≫ r = p ≫ qT` implies that
`b ≫ p` belongs to the full kernel of `qT`, so write it as `y ≫ z`. Put
`a = y ≫ z ≫ t`. The points `a` and `b` have the same image under `p`,
whereas `a` is killed by `qB`. Thus `b * a⁻¹` lies in the kernel of `p`,
and a point of `U` maps to the pulled-back `x` under `i ≫ qB`. The Library's
fppf locality of the range of a monic group-scheme homomorphism descends this
membership to the original test. The reverse kernel inclusion follows directly
from the factorization equation and exactness for `p`. This proof uses local
lifts along a scheme pullback; it assumes no surjectivity on global test-point
groups.

Both `qB` and the composite `p ≫ qT` are flat, surjective, and locally of finite
presentation. The factorization equation and descent along the flat surjection
`qB` give flatness and local finite presentation of `r`. Surjectivity of the
composite implies surjectivity of `r`. Combined with `kernel_eq`, these facts
prove `isFppfQuotient`.

Finally, `i ≫ qB` and `kernelι r` are monic representatives of the same full
subgroup functor, so the Library gives an isomorphism `U ≅ kernel r` compatible
with their inclusions. If `D` is separated over `S`, the actual kernel
inclusion is closed. Composing it with this isomorphism proves
`inclusion_isClosedSubgroup`.

All sections and quotient homomorphisms in this result are supplied. The module
does not construct Borel or unipotent data, prove a torus presentation or a
vector-bundle filtration, or prove cocycle vanishing or the semilocal inner-form
theorem. No separate centrality assumption is used: the supplied quotient
homomorphisms and their full-kernel equalities are the exact hypotheses needed
for this conditional construction.
