# Renard A.V.2: unit, counit and the two Hom maps

Authors: Workers 709 and 185.

This statement family concerns the unit–counit assertions in David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, Appendix A.V.2, printed p.259 / one-based PDF265.
The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source's preceding natural-Hom-isomorphism definition is on
printed p.258 / PDF264.

The Lean namespace is `Langlands.Renard.UnitCounit`. Every component
is a closed `Prop` definition with independent universes
`vA,uA,vB,uB`. Each binds actual categories `A : Type uA`,
`B : Type uB` with Hom universes `vA,vB`, and actual functors
`G : B ⥤ A`, `F : A ⥤ B`. There are no smallness relations,
additive or abelian assumptions, finiteness conditions or
nonemptiness assumptions.

Mathlib's `adj : G ⊣ F` means that `G` is the left adjoint and
`F` the right adjoint. Its unit has type `𝟭 B ⟶ G ⋙ F` and
its counit has type `F ⋙ G ⟶ 𝟭 A`; Lean's functor composition
lists the first-applied functor first. For arrows, `f ≫ g` means
`g ∘ f`: first apply `f`, then `g`. The associated
`adj.homEquiv Y X` goes from `Hom_A(G(Y),X)` to `Hom_B(Y,F(X))`.
This is the direction of the source's reverse-construction map on
PDF265. The initial natural isomorphism on PDF264 has the opposite
direction, represented here by the inverse equivalence.

`UnitCounitStatements` is the right-associated conjunction of the
following seven closed components, in this order.

1. `UnitCounitAtIdentitiesStatement` identifies the unit at `Y`
   as the image of `𝟙 (G.obj Y)` under `adj.homEquiv Y (G.obj Y)`.
   It identifies the counit at `X` as the image of `𝟙 (F.obj X)`
   under `(adj.homEquiv (F.obj X) X).symm`. Each identity is
   quantified independently over its appropriate objects.
2. `UnitCounitNaturalityStatement` gives the two component
   equalities for every actual arrow `f : Y ⟶ Y'` in `B`
   and every actual arrow `g : X ⟶ X'` in `A`:
   `f ≫ η(Y') = η(Y) ≫ F(G(f))` and
   `G(F(g)) ≫ ε(X') = ε(X) ≫ g`.
3. `TriangleIdentitiesStatement` gives, first, source (A.V.2.1),
   `η(F(X)) ≫ F(ε(X)) = 𝟙 (F(X))`, and then (A.V.2.2),
   `G(η(Y)) ≫ ε(G(Y)) = 𝟙 (G(Y))`. These hold for every
   `X` and every `Y`, respectively.
4. `HomEquivFormulasStatement` identifies the actual forward Hom
   equivalence with `h ↦ η(Y) ≫ F(h)` and its inverse with
   `k ↦ G(k) ≫ ε(X)`. Here `h : G(Y) ⟶ X` and
   `k : Y ⟶ F(X)`. This records the explicit maps in the
   source's converse passage.
5. `HomMapNaturalityStatement` starts with arbitrary actual natural
   transformations `η : 𝟭 B ⟶ G ⋙ F` and
   `ε : F ⋙ G ⟶ 𝟭 A`, without triangle assumptions.
   It expresses simultaneous contravariance in `Y` and covariance
   in `X` of both raw maps. For `f : Y' ⟶ Y` and
   `g : X ⟶ X'`, applying the first map to
   `G(f) ≫ h ≫ g` agrees with precomposing its value by `f`
   and postcomposing by `F(g)`. Applying the second map to
   `f ≫ k ≫ F(g)` agrees with precomposing its value by
   `G(f)` and postcomposing by `g`. The Lean equalities display
   every composition, with no replacement Hom maps assumed.
6. `HomMapInverseIdentitiesStatement` starts with those actual
   natural transformations and assumes exactly both component
   triangle identities. It asserts independently for every
   `h : G(Y) ⟶ X` and every `k : Y ⟶ F(X)` that
   `G(η(Y) ≫ F(h)) ≫ ε(X) = h` and
   `η(Y) ≫ F(G(k) ≫ ε(X)) = k`. These are both inverse
   identities claimed in the source.
7. `AdjunctionFromUnitCounitStatement` starts with the same actual
   transformations and both triangles, and concludes
   `∃ adj : G ⊣ F, adj.unit = η ∧ adj.counit = ε`.
   It preserves the supplied transformations exactly, expressing
   the source's concluding definition of an adjunction quadruple
   in Mathlib's native structure.

The source's counit paragraph prints the identity at `F(Y)`,
although the bound object is `X : A`. The identity used here is
at `F(X)`, as required by its type. This is a type-driven
correction, not a new hypothesis or an attributed author correction.
The supplementary older-edition author errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF18–19 were read. The 2026 original governs this family.

All proposition names, closed quantification, grouping and native
adjunction encoding are internal formal packaging. The first four
components use an actual native adjunction, whose data already
contain unit, counit and triangles. Their purpose is to record the
source's component assertions and exact Hom formulas at that interface.
The last three components expose the source's raw natural
transformations, naturality and converse without assuming an
adjunction in advance. The seven components are statements only.

The comparison of Renard's actual two-variable Hom-bifunctor
definition with this native adjunction is a separate obligation over
the published Hom foundation. In particular, this family alone does
not assert that a supplied natural isomorphism between those
bifunctors yields the displayed native adjunction. The A.V.1
representability and uniqueness assertions, A.V.2 preservation, and
the scalar-extension example are separate units.

The only import is Mathlib's actual
`Mathlib.CategoryTheory.Adjunction.Basic`, at pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. No proof of this
aggregate is supplied here. A separate proof must target its
unchanged published declaration after independent statement review
and Library publication.
