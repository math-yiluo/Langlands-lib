# A normal basis for a specified standard split component

`StandardBasisForComponentStatement` concerns a connected reductive group
over a nonarchimedean local field, a maximal split torus, a generic
cocharacter, a standard parabolic and a specified compatible split component
of its Levi. It asserts the existence of a subgroup `K₀` and a compact-open
normal basis at the identity of the ambient group. Every basis member
satisfies `StandardParabolicBasisMember` for the specified component, including
Iwahori decomposition, the chamber contractions and their cofinality.

`SimultaneousStandardBasisAt.exists_basis_for_component` extracts the basis
at the same `K₀` from any simultaneous standard basis. The theorem
`exists_standard_basis_for_component` proves the existence statement by
obtaining the simultaneous basis from `jointSpecialCompactBasisExistence`.

The proof represents both split components in the canonical standard Levi by
`isSplitComponent_standardComponentSchemeHom`. The universal property
`IsSplitComponent.exists_factor` factors the specified component through the
component of the simultaneous basis. Both maps into the maximal split torus
then agree along this factorization by cancellation of the torus inclusion.
Naturality of the common uniformizer section and equality of the restricted
root pairings put each point of the new weak chamber in the original weak
chamber. The original basis gives Iwahori decomposition and weak contraction
there. `IsCompatibleStandardSplitComponent.contractionAndCofinality_of_weak`
supplies the remaining contraction and cofinality conditions.

This is a change of split component in the simultaneous basis of Renard,
Théorème V.5.2(i)–(iv) (French version dated 9 July 2026, printed p. 123).
