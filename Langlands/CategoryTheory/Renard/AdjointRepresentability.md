# Renard A.V.1: proofs of representability and uniqueness of adjoints

Authors: Worker 1158 (proof implementation, source and dependency verification,
documentation); Worker 923 (supplied proof route and prior private proof
skeleton). The statement pair is imported unchanged.

This pair proves the unnumbered theorem and corollary of David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, Appendix A.V.1, printed pp.258–259 / one-based PDF264–265.
The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF18–19. Those pages give nearby older-edition corrections
but no correction to this theorem or corollary; the 2026 original governs.

All four theorems are in
`Langlands.Renard.AdjointRepresentability`. They prove the corresponding
closed proposition definitions in the published
`Langlands.CategoryTheory.Renard.AdjointRepresentabilityStatements` module.
The four levels `vA, uA, vB, uB` remain independent and arbitrary, and every
category and functor parameter is quantified inside the statement. There are
no additional hypotheses or section parameters.

## Representability criterion

`rightAdjointRepresentability` proves
`RightAdjointRepresentabilityStatement`: for `G : B ⥤ A`,

```text
(∃ F : A ⥤ B, Nonempty (G ⊣ F)) ↔
  ∀ X : A, (G.op ⋙ yoneda.obj X).IsRepresentable.
```

The presheaf at `op Y` has value `G.obj Y ⟶ X`, and acts by
precomposition with `G.map`. Its source Hom universe is `vB` and its
value universe is `vA`. The proof introduces no lift or relation between
these levels.

For necessity, unpack the given functor and actual adjunction `adj : G ⊣ F`.
Apply `Functor.rightAdjointObjIsDefined_of_adjunction adj X`. The conclusion
is definitionally the desired representability of the Hom presheaf. The
Mathlib lemma uses `adj.representableBy X`: its representing object is
`F.obj X` and its representation equivalences are
`(adj.homEquiv Y X).symm`. This agrees with Renard's necessity argument and
with the direction of his displayed Hom equivalence.

For sufficiency, suppose only that each Hom presheaf is representable.
Rewrite the goal `G.IsLeftAdjoint` using
`Functor.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top`.
Predicate extensionality reduces the resulting equality to the supplied
representability assertion at every `X`. Install this proved proposition
as a local instance, and return the actual functor `G.rightAdjoint` with
the actual adjunction `Adjunction.ofIsLeftAdjoint G`.

This use of Mathlib supplies the functor construction, rather than assuming
functorial choices of representing objects. In the pinned Mathlib source,
the reverse implication in that criterion selects representation data
objectwise and invokes `Adjunction.adjunctionOfEquivRight`. If
`R_X` represents the presheaf at `X`, the representation equivalences
`e_{Y,X} : (Y ⟶ R_X) ≃ (G.obj Y ⟶ X)` have the naturality needed by
that constructor after inversion. For `f : X ⟶ X'`, the constructed
arrow `R_X ⟶ R_X'` corresponds, under `e_{R_X,X'}`, to
`e_{R_X,X}(𝟙 R_X) ≫ f`. The constructor proves functoriality and the
adjunction identities. `IsLeftAdjoint` records existence of this functor
and adjunction; the final extraction uses classical choice.

Renard instead obtains sufficiency by taking a quasi-inverse of the fully
faithful Yoneda embedding on the full subcategory of representable
presheaves and composing it with the Hom-presheaf functor. The implemented
proof uses the representation-equivalence constructor above. It does not
implement that quasi-inverse construction.

## Uniqueness

`rightAdjointUniqueness` proves `RightAdjointUniquenessStatement`. From
`adj : G ⊣ F` and `adj' : G ⊣ F'`, the Mathlib construction
`adj.rightAdjointUniq adj'` supplies an actual natural isomorphism
`F ≅ F'`. The proof places it in `Nonempty`.

`leftAdjointUniqueness` proves `LeftAdjointUniquenessStatement` in the
same way, using `adj.leftAdjointUniq adj'` for adjunctions
`G ⊣ F` and `G' ⊣ F`, giving `G ≅ G'`.

In the pinned `Mathlib.CategoryTheory.Adjunction.Unique` source, these
constructions use the conjugation equivalence for adjunctions applied to
the identity natural isomorphism of the fixed adjoint. They include natural
transformations in both directions and both inverse identities. Thus the
witnesses give natural isomorphisms of functors, beyond separate
isomorphisms of their object values. The statements assert existence of
such an isomorphism, without asserting equality of every possible
isomorphism between the functors.

## Assembly and scope

`adjointRepresentability` proves exactly
`AdjointRepresentabilityStatements.{vA,uA,vB,uB}` by assembling the three
named proofs in the published right-associated conjunction order:
the criterion, right uniqueness, then left uniqueness.

The theorem and corollary are from Renard. The closed proposition names,
independent universes, native Mathlib adjunctions and `Nonempty` wrappers
are the published internal formal packaging. The implementation reuses
public Mathlib results by Lean name and leaves their definitions and the
published statement pair unchanged.

This pair proves the native adjunction statements only. The comparison with
Renard's definition by a natural isomorphism of two-variable Hom
bifunctors remains a separate obligation, as do the A.V.2 unit–counit and
limit-preservation families, the scalar-extension example, A.III
Yoneda/universal-arrow results and A.IV families. Their existing owners and
the whole-book obligations remain in place. This pair does not close A.V
or the whole-book parent.
