# Quotients by finite flat subgroups whose cosets lie in affine opens

## Group schemes over an arbitrary base

`Langlands.GroupScheme.exists_quotient_of_finite_flat_normal_subgroup_of_affine_cosets`
takes a group scheme `G` over a scheme `S` and a homomorphism `i : N ⟶ G` from a
group scheme `N`. It assumes that:

- the underlying morphism of `i` is a monomorphism;
- `N` is finite, flat and locally of finite presentation over `S`;
- the range of `i` is normal on all tests;
- every right coset lies in an affine open (`haff`).

The cosets are those of the Library coset relation `HomogeneousCosetRelation`, whose
arrows are `G ×_S N`. Its source is `(g, n) ↦ g` and its target is `(g, n) ↦ g · i(n)`.
The condition `haff` says that for each point `x` of `G` there is an affine open
containing the targets of all arrows with source `x`.

The theorem produces a group scheme `Q` over `S` and a homomorphism `q : G ⟶ Q`
with the following properties:

- the underlying scheme morphism of `q` is finite;
- `q` is an fppf quotient by the range of `i` (`RelativeRoot.IsFppfQuotient`), so it is
  flat, surjective and locally of finite presentation, and its full scheme kernel equals
  the range of `i` on all tests;
- the coset relation is the kernel pair of `q` as an actual pullback square of schemes.

The proof follows the Library's affine construction
`exists_affine_quotient_of_finite_flat_normal_subgroup`. That construction uses the
affine quotient theorem. This proof uses the ported FLT theorem
`AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation`
instead (Stacks 07S6 when every class lies in an affine open). That theorem needs
`haff` in place of affineness of `G`. The source and target of the coset relation are
finite, flat and locally finitely presented: the source by base change from `N`, the
target through the published translation automorphism. The Library's
`scheme_arrow_unique` and `scheme_equivalence` supply joint monicity and the
equivalence relation on all scheme tests. The structure map descends through the
coequalizer. The coset criterion from the pullback square lets `NormalQuotient`
descend the group law and makes `q` a homomorphism.

`isCommMonObj_of_epi_tensorHom` proves that the target of a homomorphism out of a
commutative group scheme is commutative when `q ⊗ q` is an epimorphism. The proof
cancels `q ⊗ q` from both sides of the commutativity equation.
`epi_tensorHom_of_flat_surjective` supplies this epimorphism for flat, surjective,
quasi-compact `q`, since `q ⊗ q` is a composite of base changes.

## Abelian schemes over a field

`Langlands.AbelianScheme.exists_abelian_quotient_of_finite_subgroup` takes an abelian
scheme `A` over an arbitrary field `K` and a monomorphic homomorphism `i : N ⟶ A`
from a finite group scheme `N`. It assumes that the cosets lie in affine opens as
above. It produces an abelian scheme `B` and a homomorphism `q : A ⟶ B` with the same
three properties: finiteness, the fppf quotient property for the range of `i`, and
the kernel-pair square.

Over a field, `N` is flat and locally of finite presentation. The range of `i` is
normal because `A` is commutative. The target is commutative by the lemma above and
smooth by the Library theorem `IsFppfQuotient.smooth_target`. Properness and geometric
connectedness descend from `A` along the finite surjection `q`, using
`UniversallyClosed.of_comp_surjective` and the published lemmas
`isSeparated_of_comp_of_surjective_of_universallyClosed` and
`geometricallyConnected_of_comp_of_surjective`. These lemmas do not use étaleness of
`q`, and the subgroup need not be étale or reduced.

The structure `AbelianQuotientData A i` packages these three properties together with
the quotient abelian scheme (`quotient`) and the homomorphism (`projection`).
`abelianQuotientData A i haff` chooses such data by classical choice on the existence
theorem. No uniqueness is asserted.

This is an internal construction from published Library results and the ported FLT
quotient theorem. It is used for the translation stabilizer of a complete linear
system in Lefschetz's cubic separation theorem.
