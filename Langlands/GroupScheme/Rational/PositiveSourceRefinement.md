# Whole-torus centralizer refinement preserving actual source weights

This derived unit applies the finite-family compatible-cocharacter construction
to actual weights of an equivariant monomorphic subgroup over a splitting
extension. The finite family comes from the published finiteness of the ambient
action-weight support. The proof uses no new literature claim.

For fields `k` and `K` in universe `u` and an algebra structure `k → K`,
`extendedSourceWeightForm f χ` is an additive integral form on the actual
cocharacter lattice of a specified commutative group scheme `A`. It first
postcomposes with the supplied map `f : A → T`, then base changes to `K`, then
pairs with the actual character `χ` of `T_K`. Its application lemma is the
defining equality. No injectivity or compatibility with an ambient embedding is
required to define this form.

Let `U` and `G` be affine group schemes over `k`, with `G` locally of finite type.
Supply an actual homomorphism `t : T.toGrp → G`, an action `d` of `T.toGrp` on
`U`, and a monomorphic homomorphism `i : U → G` equivariant for `d` and
conjugation along `t` on every test scheme. Assume `T_K` is split. Also supply a
split torus `A`, any homomorphism `a : A.toGrp → G`, the map `f : A → T`, and a
cocharacter `ν` of `A` on which every extended source-weight form is strictly
positive whenever its intrinsic source weight space over `K` is nonbottom.

`IsSplitTorus.exists_compatible_cocharacter_positive_on_source` constructs a
cocharacter `ζ` of the same `A` whose ambient dynamic centralizer equals the
whole-torus centralizer of `a`, whose dynamic parabolic lies in that of `ν`,
whose dynamic unipotent contains that of `ν`, and which is strictly positive
on every original intrinsic source weight through the extended form. These are
subgroup-functor assertions on every test scheme.

The proof base changes equivariance, compares intrinsic source weights with
the ambient support of the actual range of `i_K`, and enumerates that finite
support. It applies the finite-family refinement with the extended integral
forms. Every nonbottom source weight belongs to the enumerated support, so its
original strict positivity is retained. The empty support is allowed.

`compatiblePositiveSourceCocharacter` chooses the actual cocharacter by
classical choice. Its `_spec` theorem proves the full centralizer equality,
the two dynamic inclusions, and the strict source positivity for that chosen
value. There is no uniqueness or canonical-choice assertion.

For this general refinement, no finite-degree or Galois assumption on `K/k`, reductivity, smoothness or
connectedness of `U` or `G`, monicity of `a`, or compatibility equation between
`a`, `f` and `t` is assumed here. In an application those maps can be the
specified component embedding and its lift. The construction retains the
splitting extension, equivariant source inclusion, and initial positive
cocharacter. It does not prove their geometric existence or
`MinimalParabolicLeviCentralizerStatement`.

For the normalized-source application, let `M` be smooth, connected and affine,
let `T` also be affine, and supply a monomorphic `t : T.toGrp → M`, a map
`j : M → G`, an action `d` of `M` on `U`, and a monomorphic `i : U → G`
equivariant for that action and conjugation along `j`. Supply the original
specified split component `a : A.toGrp → M` and a lift `f : A → T` with
`groupHom f ≫ t = a`. Suppose `K/k` is finite Galois with a finite enumeration
of its automorphisms, `T_K` is split with the published relative root-system
realization for `t_K`, and an actual cocharacter of `T_K` is strictly positive
on all nonbottom source weight spaces for the restricted action of `T_K`.

`IsSplitComponent.exists_centralizingPositiveSourceCocharacter` first applies
normalized positive descent to obtain a positive integral cocharacter of `A`
over `k`. It restricts equivariance along `t` and applies the general
source-weight refinement. Compatibility of restriction with base change
identifies the two descriptions of each source weight space. The resulting
cocharacter has dynamic centralizer equal to the whole-torus centralizer of
`a ≫ j` and retains strict positivity on every original source weight over `K`.
`IsSplitComponent.centralizingPositiveSourceCocharacter` chooses this actual
cocharacter, and its `_spec` theorem proves these two properties. The two dynamic
inclusions are available in the general refinement theorem; the final
specified-component constructor records only its full centralizer and positivity.

This application retains all hypotheses of normalized positive descent and
adds local finite type of `G` for finiteness of the actual support. It preserves
the original component and lift. It does not identify their ambient centralizer
with a supplied Levi, prove ambient maximal splitness, or construct a radical
factorization, splitting field, root system or initial positive direction.
