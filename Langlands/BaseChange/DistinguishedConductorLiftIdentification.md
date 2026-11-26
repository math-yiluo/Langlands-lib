# Identification of the upper distinguished component in the conductor argument

`DistinguishedConductorLiftIdentificationStatement` takes the Library
uniqueness proposition for irreducible sigma-lifts. It takes a cyclic
extension of nonarchimedean local fields with characteristic-zero base
and the relative module topology on the upper field. The lower action
is irreducible and admissible. The admissible upper action is equivalent
to the full normalized orbit product of an irreducible supercuspidal
first block, with the supplied rank reindexing. These actions satisfy
the Library's sigma-lift identity.

The actual finite completions of the number fields are related to the
original fields by bicontinuous isomorphisms compatible with the scalar
embedding and the specified automorphisms. The actual admissible local
components satisfy `IsLiftAtDistinguishedCompletion`, and the upper
component is irreducible. The actual lower component is an unramified
determinant twist of the transported lower action. The conclusion
identifies the actual upper component with the determinant twist of the
transported upper action by the norm pullback of that character. It also
asserts that the norm pullback is unramified.

Irreducibility of the reindexed orbit product allows application of
`distinguishedSigmaLiftMatch`. The unramified conclusion follows from
the normalized order formula for the completed norm.

Arthur–Clozel identifies the distinguished lower component with the
prescribed local representation and uses local lift uniqueness to identify
the upper component in Chapter 1, Proposition 6.9(ii), printed p. 69
(PDF p. 83), literature ID `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
The conditional comparison extends that step to the supplied unramified
determinant twist using `distinguishedSigmaLiftMatch`. The Library lemma
`completion_unramified_comp_norm` gives the unramifiedness conclusion.
