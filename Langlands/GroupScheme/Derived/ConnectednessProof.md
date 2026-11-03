# Connectedness of the scheme-theoretic derived subgroup

The theorem `Langlands.GroupScheme.derivedSubgroupConnectedness.{u}` proves
exactly the published proposition
`Langlands.GroupScheme.DerivedSubgroupConnectednessStatement.{u}` from
`Langlands.GroupScheme.Derived.StructureStatement`.
For an arbitrary field `k : Type u`, an affine locally finite type group
scheme `G` over `Spec k`, and any actual homomorphism `d : D ⟶ G`
satisfying `IsDerivedSubgroup d`, connectedness of `G` implies connectedness
of `D`. The universe is arbitrary, and there is no smoothness or perfection
hypothesis.

## Source and provenance

The source assertion is J. S. Milne, *Algebraic Groups* (2017), registered
source `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
Definition 6.16, Proposition 6.18 and Corollary 6.19(b), printed p.129 /
PDF p.145. The adjacent affine coordinate discussion is on printed p.130 /
PDF p.146. The complete registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
has no displayed correction concerning Corollary 6.19(b).

The proof below is an internal argument for the Library's formulation by
the intersection of actual closed commutator-containing subgroup functors.
It uses the resulting minimality directly. It does not require a new
identification with a source-defined quotient or a separate construction
of the derived subgroup, because the target already quantifies over an
exhibiting inclusion `d`.

## Implemented proof

The private lemma `exists_connected_clopen_subgroup` constructs the identity
component as an actual group scheme for any quasi-compact locally finite
type field group `H`. It applies the published theorem
`GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent`
to the relative group law of `H`. This supplies an open and closed immersion
`i : P₀ ⟶ H.X.left`, an irreducible source, a relative group law on `P₀`,
and compatibility with multiplication. The proof transports that law to a
`GrpObj` using `RelativeGroupLaw.grpObjOverMk`. Multiplicative compatibility
gives the homomorphism law, and cancellation in the pointwise group gives
preservation of the unit. The resulting inclusion `j : P ⟶ H` is an actual
group-scheme homomorphism, its source is connected, and its topological
range is the connected component of the identity point. This application
of the relative-group-law theorem requires no smoothness.

For the main theorem, the closed immersion `d` makes `D` affine and locally
of finite type, so the private lemma gives `j : P ⟶ D` with these properties.
The published `GroupScheme.geometricallyConnected_of_connected` makes `G`
geometrically connected. Its structure map is universally open because it
is flat over a field. The pullback connectedness instance therefore makes
`G ×_k G` connected.

Take the universal commutator morphism
`c = p₁ * p₂ * p₁⁻¹ * p₂⁻¹ : G ×_k G ⟶ G`.
The all-test containment `hd.containsCommutators`, evaluated on the two
projections, gives a morphism `f : G ×_k G ⟶ D` with `f ≫ d = c`.
The point `(1, 1)` maps to the identity of `D`: this follows by composing
with the monomorphism `d` and simplifying the commutator. The connected
image lemma `IdentityComponent.range_subset_identitySet` then puts the
range of `f` inside the range of `j`.
`FiniteEtaleImage.liftOver` factors `f` through the open immersion `j`.

The composite `j ≫ d` is a closed subgroup of `G` containing every
commutator on every test scheme: for any `x, y : T ⟶ G.X`, precompose the
factorization of `c` with `lift x y`. This argument includes nonreduced
test schemes; the open-immersion factorization is a factorization of
scheme morphisms, not only of points.

Finally, `hd.range_le` puts the full range functor of `d` inside that of
`j ≫ d`. Evaluate this inclusion at the universal element
`d : D.X ⟶ G.X` to obtain a morphism `r : D.X ⟶ P.X`.
Cancellation of the monomorphism `d` gives `r ≫ j = 𝟙 D.X`.
Thus `j` is surjective on underlying topological spaces, and
`Function.Surjective.connectedSpace` transfers connectedness from `P` to `D`.
