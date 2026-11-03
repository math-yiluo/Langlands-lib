# Induced standard intersection terms on exact K0

This internal construction assembles three existing exact-K0 equalities for
actual normalized smooth functors. It works with any actual subgroup family
and independent group, root-index and carrier universes. It makes no new
literature assertion.

For coarse source and target indices `J` and `I`, fine indices are literally
`Ks : Finset J` and `Kt : Finset I`. The semidirect decompositions inside the
two coarse Levis are the `subgroupOf` restrictions of the ambient families at
`leviIndex J Ks` and `leviIndex I Kt`. The fine Levis are included in the
respective coarse Levis. The supplied membership equivalence for `n : G`
identifies the target fine Levi with the source fine Levi through
`x ↦ n⁻¹ * x * n`. All coarse Levis and ambient radicals are closed.

`inducedStandardIntersectionTermK0` follows `standardIntersectionTermK0` by
actual normalized induction from the coarse target Levi to the ambient group.
The map is integer-linear on the full exact finite-length Grothendieck groups,
with carriers in `max uG uV`. Ambient preservation and the source restricted
`ParabolicFiniteLength` family are supplied. The target restricted induction
needs only its own finite-length and short-exactness preservation.

`inducedStandardIntersectionTermK0_eq` assumes actual induction stages natural
isomorphisms at the source and target fine indices and the induced Weyl
equality between those two ambient fine inductions, with exactly the supplied
inverse-conjugation map. The proof uses
`inductionK0_comp_leviInductionK0` on the target, applies the fine-Levi Weyl
equality, and uses `inductionK0_comp_restrictedInductionK0` in reverse at the
source. Associativity gives exactly `inducedLeviAlternatingTerm` at `Ks`,
including its literal restricted Jacquet factor. The proof is an equality of
entire maps and includes all virtual finite-length classes.

The stages isomorphisms and fine-Levi Weyl equation are explicit inputs.
This generic assembly neither proves those representation-theoretic inputs
nor asserts the geometric expansion, structural twisted-intersection
identities or final rational Aubert compatibility. In particular, the Weyl
equation is an exact-K0 equality, not an assumed isomorphism of induced
representations. No classification, character-independence, adjointness,
geometric-lemma or cuspidal-support theorem is invoked by this assembly;
any later proof of its Weyl input must document its own dependencies.
