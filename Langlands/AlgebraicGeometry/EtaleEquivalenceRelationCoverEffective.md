# Arbitrary coactions on an affine quotient cover

This internal adapter constructs the pushforward of an arbitrary actual
coaction from an affine quotient cover and proves its degree-one vanishing
and invariant-lifting acyclicity. It combines the invariant-ring presentation,
effective flat descent, and source-cartesian pushforward constructions.
It introduces no additional geometric descent assumption.

Let `E'` and `E` be the published scheme étale equivalence relations in an
arbitrary universe `u`. Assume `E'.U`, `E.U`, and `E.R` affine, a morphism
given by `f : E'.U ⟶ E.U` and `g : E'.R ⟶ E.R` satisfying the published
`E'.IsCartesianHom E f g`, a closed immersion `(E.t, E.s)`, and
`hQ : E'.HasAffineQuotient`. Write

`B = Γ(E.U, ⊤)`, `C = Γ(E.R, ⊤)`,
`D = Γ(E'.U, ⊤)`, and `P = Γ(E'.R, ⊤)`.

The source maps give the algebra structures `B → C` and `D → P`,
while `f.appTop.hom` gives `B → D`. Let `M : Type (max u v)` be a
`D`-module with an arbitrary actual coaction `θ` of `E'`. The parameter
`v` is independent of the scheme universe.

`affineQuotient_oneCohomologyVanishes` first proves vanishing on the
covering relation itself. The published
`invariantPresentation_of_hasAffineQuotient` supplies faithful flatness
of `D` over the actual invariant ring of `E'`, together with an algebra
equivalence from `D ⊗ D` over that ring to `P`, carrying `1 ⊗ d` to
the target coordinate. Its inverse has exactly the target-coordinate
identity required by
`oneCohomologyVanishes_of_faithfullyFlat_presentation`. Applying that
theorem to `θ`, and using the actual ring relation supplied by
`ringRelation_of_hasAffineQuotient`, proves the claim. Only the
affineness of `E'.U`, `hQ`, and the covering module and coaction occur
in this theorem's signature.

`coverPushforward` is the actual coaction on the underlying `B`-module
`M`. Its scalar action is explicitly `Module.compHom M f.appTop.hom`,
so `b • m` means `f.appTop.hom(b) • m`. The compatible module tower
follows from associativity of the `D`-action. The `B`-action on `P`
is the composite through `D`, with its compatible ring tower.

The source-cartesian square gives the published tensor equivalence
`sourceTensorEquiv : P ≃ₐ[D] D ⊗[B] C` and its target-compatibility
identity. These, the actual base ring relation derived from affineness
and the closed immersion, and the covering ring relation derived from
`hQ` are exactly the inputs of `GroupoidCoaction.pushforward`.
That constructor cancels the covering object-ring factor in `P ⊗[D] M`
to obtain the coaction with values in `C ⊗[B] M`.

`coverPushforward_oneCohomologyVanishes` applies the published
pushforward transfer theorem to the covering vanishing proved above.
Its source and target algebra structures and module tower are the
ones used in the constructor.

Finally, `coverPushforward_isAcyclic` uses the published implication
from degree-one vanishing to the invariant-lifting predicate. The
needed flatness of `C` over `B` follows from the source étaleness of
the actual base ring relation.

Neither module finiteness nor finite, surjective, or flat behavior of
`f` is required for these conditional results. In the main application
`f` will be the given finite surjective cover. Constructing the
covering coactions needed for support induction and proving that
induction remain separate obligations; this helper does not prove the
main finite-cover acyclicity statement.
