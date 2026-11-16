# Inner-isomorphism descent through sectioned Weil quotients

This internal module combines the actual quotient construction in
`SectionedQuotientExtension`, vector-bundle series cocycle vanishing, and
fppf descent of local group isomorphisms. Its base is `Spec A` for an arbitrary
commutative ring in universe `u`. All groups, schemes, and coefficient rings
use that universe.

Supply homomorphisms `i : K → B`, `p : B → T`, `t : T → B`, and `z : Z → T`,
with `t ≫ p = id`. Supply fppf quotient homomorphisms `qB : B → P` and
`qT : T → D` by the full subgroup functors `range (z ≫ t)` and `range z`.
Also assume that `p` is an fppf quotient by `range i` and that the underlying
map of `i` in `Over (Spec A)` is monic. These quotient hypotheses include
flatness, surjectivity, local finite presentation, and equality with the full
range of the actual kernel inclusion on every relative test scheme.

Assume that `P` is affine, `K` is affine over the base and has a supplied
`RelativeUnipotent.HasFiniteVectorBundleSeries`, and supply an isomorphism
`eD : D ≅ WeilGm.groupScheme A C`. The coefficient algebra `C` is finite and
projective as an `A`-module. The original cover `V → Spec A` is a single
flat, surjective, locally finitely presented morphism. Its total space need
not be affine or quasi-compact.

The constructed homomorphism `r : P → D` is the one in
`SectionedQuotientExtension.hom`. That module proves that `i ≫ qB` is monic,
that its full range is the kernel of `r`, and that `r` is an fppf quotient.
The kernel group remains exactly `K`, with its original supplied series.
Affineness of `D` follows from `eD`. These facts discharge the extension
hypotheses of `VectorBundleWeilCocycle`, giving
`cocycle_isTrivial_of_pic_trivial` for every `P`-valued cocycle on the original
cover if `CommRing.Pic C` is a subsingleton.

`picardCochain` chooses the resulting primitive `f : V → P`.
`picardCochain_spec` gives
`ξ(a,b) = (a ≫ f) * (b ≫ f)⁻¹` for every relative test scheme and every
pair of its points of `V`. The two subsequent vanishing theorems obtain
the coefficient Picard hypothesis from finite-algebra Picard triviality
and from semi-locality of `A`, respectively.

For the isomorphism construction, supply a local group isomorphism
`e : LocalGroupIso G H V`, an action `c` of `P` on `G` by automorphisms,
its all-test faithfulness, and `e.HasInnerDiscrepancy c`. The latter only
asserts existence of a representing point of `P` for each pair of cover
points, with the action equation after every refinement. Faithfulness
constructs naturality and the cocycle law via `e.innerCocycle`; neither is
an extra hypothesis. `innerIsoOfPicTrivial` corrects the local maps with
the selected primitive and descends the independent corrected family to
an actual group-scheme isomorphism `G ≅ H`.

`innerIsoOfPicTrivial_spec` identifies that actual isomorphism on every
test scheme with a point `b` of the original cover: its value at `g` is
`e_b(c(f_b)(g))`. The generic `LocalGroupIso.comp_descendFppf_eq` proves
this evaluation rule for any independent family, using the factorization
equation for its descended natural group homomorphism.
`innerIsoOfSemilocal` supplies the Picard hypothesis over a semi-local ring.

Finally, `AutomorphicAction.IsFaithful.restrict_mono` proves that restricting
a faithful action to a monic subgroup preserves all-test faithfulness.
`centralQuotientInnerIsoOfSemilocal` uses it for an action of a supplied full
centre fppf quotient of `G` whose restriction to `G` is conjugation, and
a monic homomorphism `j : P → Gad`. The full-centre quotient action is
faithful by `RelativeInnerCocycle`. Thus this final construction only needs
pointwise inner discrepancy in the restricted action; it does not require
a separate faithfulness proof or a supplied natural subgroup cocycle.

The provenance is the internal composition and evaluation of these existing
constructions. This module does not construct a Borel, a homomorphic section,
a unipotent series, a Weil-restriction presentation, or local isomorphisms
whose discrepancies lie in the supplied subgroup. It proves no unconditional
quasi-split existence or semilocal inner-form theorem.
