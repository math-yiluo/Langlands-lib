# Off-diagonal induction for separated étale morphisms

This derived helper formalizes the diagonal-splitting and degree-reduction
step in the proof of Stacks Project Lemma 67.50.1, Tag 03XW. The registered
original is `stacks-03XW-2026-11-02`, `03XW.html`, the proof paragraphs starting
“By Morphisms, Lemma 29.58.9” and “Consider the affine scheme”.
The full page was read, including its proof and empty comments section.

For schemes in an arbitrary universe `u`, `HasFieldFibreBound e n` says that
every fibre of the map on `K`-valued points is finite of cardinality at most
`n`, for every field `K : Type u`. The finiteness conjunct is essential because
`Nat.card` is zero on infinite types. The published affine étale point bound
supplies such a bound whenever the source and target are affine.

An étale morphism with bound one is an open immersion. The proof first makes
each field-valued fibre a subsingleton, then uses Mathlib's field-valued
criterion for universal injectivity. Its diagonal is therefore surjective.
The diagonal is also an open immersion by étaleness, so it is an isomorphism.
The morphism is consequently a monomorphism; Mathlib's theorem on flat
monomorphisms locally of finite presentation gives the open immersion.
No affineness or separatedness hypothesis is used for this conclusion.

For a separated étale morphism `e : T ⟶ Y`,
`EtaleOffDiagonal.openComplement e` is the open subset complementary to the
range of its diagonal inside the actual scheme pullback `T ×[Y] T`.
The diagonal is closed by separatedness and open by étaleness, so this
complement is clopen. `EtaleOffDiagonal.scheme e` is its actual open
subscheme. Its inclusion is also a closed immersion, and the scheme is
affine when both `T` and `Y` are affine. Its first projection to `T` is
étale and separated.

`EtaleOffDiagonal.hasFieldFibreBound` proves that a bound `n + 1` for `e`
gives a bound `n` for this restricted first projection. In a fibre over a
map `a : Spec K ⟶ T`, the second projection gives an injective map into
the fibre of `e` over `a ≫ e`. It never equals the distinguished lift `a`:
otherwise the pullback universal property would factor the off-diagonal
point through the diagonal. Evaluation at the unique closed point of
`Spec K` contradicts membership in the complement. Adjoining the
distinguished lift therefore gives an injection from the option type of
the off-diagonal fibre into the original fibre. Finite cardinality yields
the asserted decrease by one.
This cardinality argument needs only separatedness; étaleness is used for the
clopen and étale conclusions and for the bound-one criterion.

This module proves only this induction infrastructure. It does not assert
effectivity of descent or representability of algebraic spaces.
