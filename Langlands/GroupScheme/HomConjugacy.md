# Inner conjugacy of group-scheme morphisms

For group schemes `H` and `G` over an arbitrary scheme `S`, `HomConjugate χ ψ`
means that a single point `g : S → G` conjugates the morphism `χ : H → G` to
`ψ`. More precisely, it asserts `χ ≫ (G.innerIso g).hom = ψ`, an equality of
group-scheme morphisms. The direction is `g χ g⁻¹ = ψ`.

`constantPointHom T` is the existing pullback of base points, now packaged as a
group homomorphism. Its value is `constantPoint g T`, and pullback to the identity
test scheme returns `g`. `homConjugate_iff_points` identifies the scheme equality
with the conjugation formula on every test scheme and every point of `H`, using
the same base point throughout. Its reverse implication uses the established
Yoneda extensionality theorem `hom_ext_points`; complex-valued points alone are
not used to infer equality of schemes.

The relation is reflexive, symmetric, and transitive. The proofs use respectively
the identity point, the inverse point, and the product of the second conjugator
with the first. The point formulas reduce these claims to group identities;
pullback preserves identity, multiplication, and inversion. `homConjugacySetoid`
packages these proofs as an equivalence relation on actual scheme morphisms.

This is an internal construction from `InnerAutomorphism` and the group-valued
Yoneda functor. It adds no hypotheses about affine representability, smoothness,
reductivity, or classification of cocharacters, and uses no additional source.
