# Existence of the actual maximal-torus parameter scheme

Worker 633, using the statement and source route specified by Workers 1337
and 1574.

`Langlands.GroupScheme.MaximalTorusParameterExistenceStatement.{u}` is a
Prop-valued statement for arbitrary universe `u`. It quantifies over every
field `k : Type u`, every group scheme `G` over `Spec k` whose structure
map is smooth and affine and whose underlying space is connected, and
every maximal torus `j₀ : T₀.toGrp ⟶ G`. Its conclusion is the existence of
one actual `k`-scheme `Q : Over (Spec k)` and one actual morphism
`q : G.X ⟶ Q` satisfying the published predicate
`IsMaximalTorusParameter j₀ q`.

That predicate supplies all of the following properties of these same
`Q` and `q`:

1. `Q.hom` is smooth, separated, locally of finite type and quasi-compact.
   The last two properties express finite type.
2. `q.left` is smooth, surjective and quasi-compact.
3. For every scheme test `U : Over (Spec k)` and every pair of morphisms
   `g h : U ⟶ G.X`, equality `g ≫ q = h ≫ q` is equivalent to
   `g⁻¹ * h ∈ (torusNormalizer j₀).carrier U`.
4. `TorusParameterConjugationCompatible j₀ q` holds for this map.

The only assumptions on the field and group are those displayed above.
In particular, the statement applies to finite and imperfect fields and
to nonreductive smooth connected affine groups. It imposes no splitness,
characteristic, rationality or unirationality condition.

The original representability result is SGA3, Tome II, Expose XII,
Corollaire 1.10, together with Theoreme 1.7. In the retained Gille-Polo
December 2008 recomposition, `Expo12.pdf`, these are one-based PDF pages
4–6, printed pages 122–124 (original pages 185–188). Corollaire 1.10 states
that, for a smooth affine group with locally constant reductive rank,
the functor assigning to each base scheme the maximal tori of the
base-changed group is represented by a smooth separated scheme of finite
type. The rank condition is automatic over `Spec k`. Its proof identifies
the representing scheme, when a maximal torus `T₀` is chosen, with
`G/N_G(T₀)`, and identifies the projection with
`g ↦ int(g)(T₀)`. Smoothness and affineness of the Lean group structure
map imply finite type over the field, as required for this specialization.

The quotient description uses SGA3, Expose XI, Corollaires 5.1 bis–5.4 bis
and Remarque 5.5 bis, `Expo11.pdf`, one-based PDF pages 26–27, printed
pages 110–111 (original pages 166–168). The smooth orbit-map and
transporter assertions, with the quotient argument of 5.3 on PDF page
25, give the smooth surjective finite-type projection to the normalizer
quotient. This accounts for smoothness, surjectivity and quasi-compactness
of `q`. Since the quotient is by the normalizer subgroup functor, its
fiber relation on every scheme test is exactly the right-coset condition
in the imported predicate.

Representability supplies a universal closed torus
`𝒯 ⊆ G ×ₖ Q`: it is the maximal torus corresponding to the identity
map of the representing scheme. Its pullback along `q` is the family of
conjugates of `T₀`. For a rational parameter `x : Spec k ⟶ Q`, pulling
back `𝒯` along `x` therefore gives an actual closed `k`-torus
`j : T.toGrp ⟶ G`. This is a torus over the ground field even when `x`
has no lift in `G(k)`.

More precisely, extend `x` to `K = AlgebraicClosure k`. If any
`g ∈ G_K(K)` lies above this extended parameter, the defining property
of `q` and base change of the universal family identify `T_K` as the
closed subgroup `int(g)((T₀)_K)`. Equality of these actual closed
subgroups gives equality of their represented subgroup functors on
every `K`-scheme test. Consequently the same closed ground-field torus
chosen from `x` works for every such `g`, which is exactly the
quantifier order and equality required by
`TorusParameterConjugationCompatible j₀ q`. Scheme-theoretic
surjectivity of `q` asserts no surjectivity on `k`-rational sections.

Conrad, Gabber and Prasad, *Pseudo-reductive groups*, second edition
(2015), proof of Proposition A.2.11, printed pages 477–478, one-based
PDF pages 503–504, gives this concrete variety `Tor_G = G/N_G(T₀)`
and its fiberwise maximal closed universal torus. It describes the
family by descent from the conjugation embedding over `G/Z_G(T₀)`,
explains its fibers over arbitrary extension fields, and points to
SGA3 XII 1.10 for the stronger universal property on arbitrary scheme
tests. This is the unrestricted smooth connected affine field-group
setting used in the Lean statement. The later rationality and density
arguments in that proof are separate from this existence assertion.

The cited retained sources are registered as
`sga3-exposes-xi-xii-xiv-gille-polo-2008` (the folder containing
`Expo11.pdf` and `Expo12.pdf`) and
`conrad-gabber-prasad-2015-pseudo-reductive` (the second-edition PDF).
The Lean module imports the existing parameter predicate directly.
It defines the existence proposition and supplies no proof of it;
formal construction of the quotient, universal-family descent and
the compatibility field remain obligations of a proof successor.
