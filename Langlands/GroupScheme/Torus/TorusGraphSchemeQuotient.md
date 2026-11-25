# A smooth graph relation for a representation with central kernel

The declarations are in `Langlands.GroupScheme.TorusGraphQuotient`. This is an
internal construction for the valuative-lifting route to the affineness of the
quotient by the normalizer of a self-centralizing maximal torus in a smooth
separated group. It is the
scheme step of factoring a representation with a possibly nonsmooth central
kernel. It uses the Library's smooth-relation quotient construction, not a
quotient theorem for a nonsmooth relation.

Let `G`, `L` be group schemes and `T`, `D` commutative group schemes over a
base scheme `S`. Take homomorphisms `t : T ⟶ G`, `π : T ⟶ D`, `ρ : G ⟶ L`
and `e : D ⟶ L`. The definition `graph t π` is the group homomorphism
`τ ↦ (t(τ), π(τ)⁻¹)` into `G ×ₛ D`: inversion in `D` preserves the group law
because `D` is commutative. The first projection shows that the graph map
is monomorphic if `t` is. The relative *scheme* map `productMap ρ e` sends
`(g,d)` to `ρ(g)e(d)`; it need not preserve multiplication.

Suppose the kernel of `ρ` is central on every scheme test, `t` represents its
own centralizer, `π` is flat, surjective and locally of finite presentation,
`e` is monomorphic as a relative scheme map, and `π ≫ e = t ≫ ρ`.
`exists_graph_coordinate` upgrades the Library's
`exists_torus_point_of_comp_eq`: a test point `y` of `G` with
`ρ(y) = e(d)` is `t(τ)` for a point `τ` of `T`, and `π(τ) = d` by
cancellation through `e`.

For `productMap_fibers`, equality of the images of `(g,d)` and `(h,d')`
says `ρ(g⁻¹h) = e(dd'⁻¹)`. The previous lemma gives a point `τ` of `T` with
`t(τ) = g⁻¹h` and `π(τ) = dd'⁻¹`. Thus the point `(g⁻¹h,d⁻¹d')` is in the
range of `graph t π`, using commutativity of `D`. Conversely, substituting
the two graph coordinates into the factorization equation gives the same
image under `productMap`. The equivalence holds over all relative scheme
tests, not just on points with values in fields.

If `G` and `D` are locally of finite type and `T` is smooth over `S`, the
choice `graphSchemeQuotient` applies `schemeQuotientOfMapKernel` to the
right-coset relation of that graph. The exact fibre comparison and
`hasSmoothProjections` give a scheme `Q` over `S`, a smooth surjective map
`p : G ×ₛ D ⟶ Q`, and a map `m : Q ⟶ L` whose underlying morphism is
monomorphic and for which `p ≫ m = productMap ρ e`. Neither ambient
affineness nor smoothness of `ker ρ` is needed. The module does not equip
`Q` with a group law, assert flatness of the induced `G ⟶ Q`, or prove the
valuation-ring extension or affine conjugacy quotient statements.
