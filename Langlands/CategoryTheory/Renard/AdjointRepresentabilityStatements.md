# Renard A.V.1: representability and uniqueness of adjoints

Authors: Worker 709 (statement design, implementation and
documentation); Worker 923 (independent source and API recheck,
inspection checks and documentation edits).

This pair states the unnumbered theorem and its corollary in David
Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, Appendix A.V.1. The theorem starts on
printed p.258 / one-based PDF264 and concludes, with its proof and
the corollary, on printed p.259 / PDF265. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The namespace is `Langlands.Renard.AdjointRepresentability`. All four
declarations are closed `Prop`-valued definitions. This pair supplies
statements; their proofs remain separate obligations.

## Actual data and universes

Every component internally binds categories `A : Type uA`,
`B : Type uB`, with `[Category.{vA} A]` and `[Category.{vB} B]`.
The four levels `vA,uA,vB,uB` are independent. The statements
use actual Mathlib functors, adjunctions, representable presheaves
and natural isomorphisms. They assume no finiteness, completeness,
nonemptiness, additive structure or relation between category universes.

The source writes `G : B → A` for the left adjoint and `F : A → B`
for the right adjoint. These are `G : B ⥤ A`, `F : A ⥤ B` and
`G ⊣ F` in Lean. Mathlib's actual adjunction contains a unit
`𝟭 B ⟶ G ⋙ F`, a counit `F ⋙ G ⟶ 𝟭 A` and both triangle
identities; these are the source's `η : Id_B → FG` and
`ε : GF → Id_A` of A.V.2. Its derived Hom equivalence
`adj.homEquiv Y X` has direction

```text
(G.obj Y ⟶ X) ≃ (Y ⟶ F.obj X).
```

The first Hom isomorphism in the source, `θ_{Y,X} :
Hom_B(Y,F(X)) ≃ Hom_A(G(Y),X)` on PDF264, is written in the reverse
direction. Inversion relates the two directions. The source defines
adjointness as a natural isomorphism between the bifunctors
`R_F, L_G : A × Bᵒᵖ → Ens`; the theorem's "admits a right adjoint"
refers to that definition. This family uses
the native adjunction encoding. The comparison with the actual
two-variable Hom-bifunctor definition of adjunction is a separate
obligation of the whole-book program; this pair does not establish it.

For `X : A`, the actual composite

```text
G.op ⋙ yoneda.obj X : Bᵒᵖ ⥤ Type vA
```

is the presheaf occurring in the theorem, the contravariant functor
`Y ↦ Hom_A(G(Y), X)` from `B` to sets. At `op Y` its value is
`G.obj Y ⟶ X`. For `f : Y' ⟶ Y` its map takes
`h : G.obj Y ⟶ X` to `G.map f ≫ h`. Here `≫` composes
arrows from left to right, so this is the source's `h ∘ G(f)`.
It is the source bifunctor `L_G` with its `A`-variable fixed at `X`:
`L_G(id_X, f)(h) = h ∘ G(f)`. Both facts hold by definitional
equality in the checks recorded below. The source's display of
`L_G(f,g)` on PDF264 writes `Hom_B(G(Y),X)` where `Hom_A(G(Y),X)` is
meant; the theorem itself writes `Hom_A(G(Y),X)`, which is what is
formalized.

Mathlib's `Functor.IsRepresentable` on this presheaf means that
there exist an actual object `R : B` and representation data. Those
data contain, for every `Y : B`, an equivalence

```text
e_Y : (Y ⟶ R) ≃ (G.obj Y ⟶ X),
```

including both inverse identities, satisfying

```text
e_Y' (f ≫ k) = G.map f ≫ e_Y k
```

for every `f : Y' ⟶ Y` and `k : Y ⟶ R`.
Thus representability includes the required naturality, rather than
only a family of bijections. `RepresentableBy` permits its source
Hom universe `vB` and value universe `vA` to differ: the instance
used here is `Functor.IsRepresentable.{vA, vB, uB}`, and each
`e_Y` is an equivalence between a type in `Type vB` and a type in
`Type vA`. This formulation needs no universe lifts or equality of
levels. The right side is definitionally Mathlib's
`G.rightAdjointObjIsDefined X`, the domain of the partial right
adjoint of `G`.

## The three statements

`RightAdjointRepresentabilityStatement.{vA,uA,vB,uB}` binds
`G : B ⥤ A` and asserts

```text
(∃ F : A ⥤ B, Nonempty (G ⊣ F)) ↔
  ∀ X : A, (G.op ⋙ yoneda.obj X).IsRepresentable.
```

The left side concludes existence of an actual functor on both
objects and arrows and actual adjunction data. It does not assume
an already chosen right adjoint. The right side asks separately
for each object `X` that the indicated actual Hom presheaf be
representable; it assumes no functorial choices of representatives
or naturality in `X`. Obtaining such a functor from these objectwise
data is part of the theorem. In the forward direction the
representing object is `F.obj X`, and the representation equivalences
are the inverses of the native adjunction Hom equivalences.

`RightAdjointUniquenessStatement.{vA,uA,vB,uB}` binds an actual
`G : B ⥤ A`, actual `F F' : A ⥤ B` and adjunctions
`G ⊣ F` and `G ⊣ F'`. It concludes `Nonempty (F ≅ F')`.
The witness is an actual natural isomorphism: its component arrows
are natural, and it has an inverse natural transformation with both
inverse identities. Objectwise isomorphisms alone would be weaker.

`LeftAdjointUniquenessStatement.{vA,uA,vB,uB}` binds an actual
`F : A ⥤ B`, actual `G G' : B ⥤ A` and adjunctions
`G ⊣ F` and `G' ⊣ F`. It concludes `Nonempty (G ≅ G')`.
This is the dual assertion in the source corollary.

In both uniqueness statements, `Nonempty` makes existence of the
natural isomorphism propositional. The assertions express uniqueness
of an adjoint up to natural isomorphism; they do not assert that
every possible natural isomorphism between the functors is equal.

`AdjointRepresentabilityStatements.{vA,uA,vB,uB}` is exactly the
right-associated conjunction of the representability criterion,
right-adjoint uniqueness and left-adjoint uniqueness, in that order.

## Provenance and proof boundary

The mathematical criterion and both uniqueness assertions are those
of the source theorem and corollary. Their formal names, closed
quantification, independent universes, native adjunction encoding,
representation-data encoding and `Nonempty` wrappers are internal
formal packaging. No stronger uniqueness assertion or extra
representability criterion for left adjoints is claimed.

Renard proves necessity using `F(X)` as representing object and
sufficiency by the fully faithful Yoneda embedding and a
quasi-inverse on the full subcategory of representable functors.
That is the source proof, rather than a proof supplied here. A later
exact proof may instead use Mathlib's actual representability
criterion for existence of a right adjoint and its constructions
of natural isomorphisms between adjoints; its companion must
describe the implemented route.

The supplementary registered source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked on PDF18–19. Those pages contain nearby older-edition
Hom-bifunctor and scalar-extension corrections, with no correction
to this theorem or corollary. This is a bounded supplementary check;
the 2026 original governs.

This pair does not prove the aggregate, compare the two encodings
of adjunction, construct the scalar-extension example, or supply the
separate A.V.2 unit–counit and preservation families. A later proof
must target this aggregate after its unchanged Library publication.

## Checks

These are author diagnostics in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, not independent acceptance.
Worker 709's entry check `91a3d684-8ace-407a-85e3-73ab023f9575` and
full-definition check `35064c48-67c2-4ae3-8527-23ef07cd3e09` are
clean. Worker 923's entry check
`6333ff24-32c3-4c17-88fe-3c6a1ce8fd4b` reports zero errors and
warnings, `statement_returns_prop: true`, level parameters
`vA, uA, vB, uB` and only the axioms `propext`, `Classical.choice`
and `Quot.sound`. Worker 923's inspection module
`8ee55a01-78d2-449f-93df-a211e986730e` (not part of this pair)
prints all four complete definitions together with
`Functor.RepresentableBy` and `Functor.IsRepresentable`. It checks
by `rfl` the exact conjunction order and the presheaf's objects and
maps, and it checks the naturality identity above and the
`rightAdjointObjIsDefined` agreement. It elaborates the aggregate at
the unrelated level tuples `(0,1,2,3)`, `(3,0,1,5)`, `(0,0,0,0)`
and `(2,7,0,1)`.

The same module also compiles, as a non-vacuity check, a proof of the
aggregate from Mathlib's
`Functor.rightAdjointObjIsDefined_of_adjunction`,
`Functor.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top`,
`Adjunction.rightAdjointUniq` and `Adjunction.leftAdjointUniq`. That
proof is not part of this pair and is not accepted evidence.
