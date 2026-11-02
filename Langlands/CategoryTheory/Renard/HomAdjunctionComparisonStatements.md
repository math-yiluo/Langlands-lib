# Renard A.V: comparison of the two definitions of adjunction

Authors: Worker 709 and Worker 1151. Worker 709 supplied the statement
pair; Worker 1151 verified the source correspondence and complete
declarations and prepared the focused submission.

This statement family compares the two definitions of adjunction in David
Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, Appendix A.V.1–A.V.2, printed pp.258–259 / one-based
PDF264–265. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The opening of A.V explicitly identifies the two viewpoints as equivalent.
A.V.1 defines adjointness by a natural isomorphism between two Hom
bifunctors. A.V.2 obtains unit and counit from that isomorphism and gives
the converse construction from natural unit and counit satisfying both
triangle identities.

The namespace is `Langlands.Renard.HomAdjunctionComparison`. Every component
is a closed `Prop` definition that binds categories `A : Type uA` and
`B : Type uB` with category structures `Category.{vA} A` and
`Category.{vB} B`, then actual functors `G : B ⥤ A` and `F : A ⥤ B`.
The four universes `vA,uA,vB,uB` are independent. Empty categories and
arbitrary Hom sets are included.

The imported constructions in `Langlands.Renard.AdjunctionHom` are the
actual bifunctors on `A × Bᵒᵖ`, valued in `Type (max vA vB)`.
At `(X, op Y)`, `rightHomBifunctor F` is
`ULift.{vA} (Y ⟶ F.obj X)` and `leftHomBifunctor G` is
`ULift.{vB} (G.obj Y ⟶ X)`. For a product-category arrow `f : p ⟶ q`, their maps send `ψ`,
respectively, to `ULift.up (f.2.unop ≫ ψ.down ≫ F.map f.1)` and
`ULift.up (G.map f.2.unop ≫ ψ.down ≫ f.1)`. These are the actual
simultaneous precomposition and postcomposition actions. Consequently
`theta : rightHomBifunctor F ≅ leftHomBifunctor G` includes naturality
in both variables and both inverse identities. The lifts only place the
two Hom sets in a common universe; the equations below remove them with
`down`.

For a native Mathlib adjunction `adj : G ⊣ F`, `G` is the left adjoint
and `F` the right adjoint. Its unit and counit have types
`𝟭 B ⟶ G ⋙ F` and `F ⋙ G ⟶ 𝟭 A`, and its data contain both
triangle identities. The equivalence
`adj.homEquiv Y X : (G.obj Y ⟶ X) ≃ (Y ⟶ F.obj X)` runs in the
opposite direction to the initial `theta` in A.V.1. The source reuses
the name theta for the reverse-direction construction in A.V.2; this
companion uses `theta` consistently for the A.V.1 direction.

`HomAdjunctionComparisonStatements` is exactly the right-associated
conjunction of these three closed components, in this order.

1. `NativeToHomStatement` starts with every supplied native
   `adj : G ⊣ F` and concludes that there is an actual natural isomorphism
   `theta : rightHomBifunctor F ≅ leftHomBifunctor G` with both
   component formulas. For every `X : A`, `Y : B` and
   `k : Y ⟶ F.obj X`,
   `(theta.hom.app (X, op Y) (ULift.up k)).down =
   (adj.homEquiv Y X).symm k`.
   For every `h : G.obj Y ⟶ X`,
   `(theta.inv.app (X, op Y) (ULift.up h)).down =
   adj.homEquiv Y X h`.
   Thus one natural isomorphism realizes both maps for all objects and
   arrows of the given adjunction.
2. `HomToNativeStatement` starts with every supplied actual natural
   isomorphism of those same bifunctors and concludes that there is
   `adj : G ⊣ F` satisfying both of those exact component formulas.
   This preserves the supplied `theta` at both its hom and inverse
   components. The only adjunction in this component is the one whose
   existence is concluded.
3. `HomAdjunctionIffNativeStatement` asserts
   `HomAdjunction G F ↔ Nonempty (G ⊣ F)` for every such pair
   of functors. Here the imported `HomAdjunction G F` is exactly
   `Nonempty (rightHomBifunctor F ≅ leftHomBifunctor G)`.
   This existential comparison is internal packaging of the consequence
   of the preceding exact comparisons.

The full component comparisons are an internal formal expression of the
source's equivalence of viewpoints using the published Hom bifunctors
and Mathlib's native unit–counit structure. The component equalities
record the correspondence of the actual maps, beyond the existential
comparison alone. The closed quantification, names, lifts and conjunction
are internal formal packaging. No extra smallness, object or Hom universe
identifications, nonemptiness, additivity, abelian structure, finiteness,
or selected universal property is assumed.

The source's `L_G` map display on PDF264 prints `Hom_B` where the arrows
belong to `A`. The foundation uses the type-correct `Hom_A`, consistent
with the source's preceding object formula. Its counit paragraph on
PDF265 prints the identity at `F(Y)` although the bound object is
`X : A`; the correctly typed identity is at `F(X)`. These discrepancies
are documented in the foundation and unit–counit companions. The
supplementary older-edition errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read on PDF18–19. The correction for old p.299 on PDF18 still
prints `Hom_B`. The 2026 original governs this family.

The module imports the published
`Langlands.CategoryTheory.Renard.AdjunctionHom` and Mathlib's
`Mathlib.CategoryTheory.Adjunction.Basic`, pinned at commit
`5ed2965256430c3649e86755f9576b54eca72435`. It adds statements only.
The separate native unit–counit statement family records identity,
naturality, triangle, raw Hom-map and reconstruction assertions. The
present family supplies the comparison with the actual two-variable
Hom-isomorphism interface. Representability, uniqueness, preservation
and scalar extension retain their separate obligations.

No proof of these statements is supplied in this pair. A proof must
target the unchanged published declaration after independent statement
review and actual Library publication. This family makes no Appendix A
or whole-book completion claim.
