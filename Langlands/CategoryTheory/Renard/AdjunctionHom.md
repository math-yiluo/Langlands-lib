# Renard A.V.1: the Hom bifunctors

Authors: Worker 709 and Worker 1151. Worker 709 supplied the construction;
Worker 1151 verified the source correspondence and complete declarations and
prepared the focused submission.

This construction implements the two actual Hom bifunctors and the first
definition of adjoint functors in David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix A.V.1,
printed p.258 / one-based PDF264. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The namespace is `Langlands.Renard.AdjunctionHom`. Let `A : Type uA` with
`Category.{vA} A` and `B : Type uB` with `Category.{vB} B`. The four
universes are independent. For actual functors `F : A ⥤ B` and
`G : B ⥤ A`, both constructed bifunctors have domain `A × Bᵒᵖ`
and codomain `Type (max vA vB)`.

`rightHomBifunctor F` is Renard's `R_F`. At `p = (X, op Y)` its
object is `ULift.{vA} (Y ⟶ F.obj X)`. On a product-category morphism
`f : p ⟶ q`, it sends `ψ` to the lift of
`f.2.unop ≫ ψ.down ≫ F.map f.1`. Thus it precomposes with the
actual arrow `unop q.2 ⟶ unop p.2` and postcomposes with the
image of `p.1 ⟶ q.1`.

`leftHomBifunctor G` is Renard's `L_G`. Its object at the same
pair is `ULift.{vB} (G.obj Y ⟶ X)`. Its map sends `ψ` to the lift of
`G.map f.2.unop ≫ ψ.down ≫ f.1`. Both source and target arrows
of this Hom set belong to `A`.

The source's displayed map formula for `L_G` prints `Hom_B` where
`Hom_A` is required. The preceding object formula correctly uses
`Hom_A`, and `G(Y)` and `X` are objects of `A`; they need not even
be objects of `B`. The Lean construction uses this type-correct
`Hom_A` formula. The older-edition author errata, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read on PDF18–19. The correction for old p.299 on PDF18
repeats `Hom_B` and does not repair this subscript. This observation
is limited to those errata pages; the 2026 original governs.

The opposite lift parameters on the two Hom sets put them in the
same universe while preserving arbitrary, unrelated `vA` and `vB`.
Each lift has its canonical `up` and `down` bijections with the
original Hom set; neither the arrows nor their composition are
replaced by arbitrary data. The lifts are internal size packaging
for the source's common category of sets. No object-universe
equality, smallness, finiteness, nonemptiness, additivity or
abelian-category hypothesis is imposed.

`HomAdjunction G F : Prop` is
`Nonempty (rightHomBifunctor F ≅ leftHomBifunctor G)`.
It expresses the existence of the source's natural isomorphism,
with component direction
`Hom_B(Y,F(X)) → Hom_A(G(Y),X)` after removing the lifts.
The natural-isomorphism type contains the actual transformations,
their naturality laws and inverse identities. `Nonempty` makes
existence a proposition rather than choosing one isomorphism.
This is Renard's first definition: `G` is the left adjoint and `F`
the right adjoint.

The functor identity and composition laws are proved by extensionality
on lifted arrows, followed by simplification using the category laws
and the corresponding laws of `F` or `G`. The four computation lemmas
`rightHomBifunctor_obj`, `leftHomBifunctor_obj`,
`rightHomBifunctor_map_down` and `leftHomBifunctor_map_down` are
definitional equalities. These laws and computation lemmas are small
intrinsic obligations of the construction.

The module imports Mathlib's actual Hom-functor infrastructure at the
pinned Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The bifunctors and predicate names are internal formal names for
the source constructions. The comparison with Mathlib's unit–counit
type `G ⊣ F`, the representability criterion, uniqueness of adjoints,
the remaining unit–counit assertions, preservation, and the
scalar-extension example are separate statement and proof
obligations. This construction does not prove those results.
