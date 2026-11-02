# Renard A.V: proof of the comparison of the two definitions of adjunction

Worker 1172 proves the published closed proposition
`Langlands.Renard.HomAdjunctionComparison.HomAdjunctionComparisonStatements.{vA,uA,vB,uB}`,
imported from `Langlands.CategoryTheory.Renard.HomAdjunctionComparisonStatements`.
The final theorem is
`Langlands.Renard.HomAdjunctionComparison.homAdjunctionComparisonStatements`.
Its type is exactly the closed aggregate at the four independent universe
levels `vA,uA,vB,uB`. It has no extra assumptions or parameters.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The passage is Appendix A.V.1–A.V.2, printed pp.258–259 / one-based
PDF264–265. Both pages were read for this proof. The opening of A.V says that
the two viewpoints on adjoint functors are equivalent. A.V.1 defines
adjointness by a natural isomorphism `θ : R_F ≅ L_G` of Hom bifunctors.
A.V.2 obtains a unit and a counit from it as the images of identity arrows,
and conversely builds mutually inverse natural Hom maps from a unit and a
counit satisfying both triangle identities. Renard gives no further written
proof. The proof below is the standard argument through Mathlib's
construction of an adjunction from a natural Hom equivalence.

## Conventions

The statement companion explains the source-to-Lean formulation and is
unchanged. Renard's `G : B → A` is the left adjoint and `F : A → B` the right
adjoint, so the native adjunction is Mathlib's `adj : G ⊣ F`. In Lean
`f ≫ g` means `g ∘ f`. At `(X, op Y)` the published bifunctors take the
values `ULift.{vA} (Y ⟶ F.obj X)` and `ULift.{vB} (G.obj Y ⟶ X)` in
`Type (max vA vB)`. For an arrow `f` of `A × Bᵒᵖ` they send `ψ` to
`ULift.up (f.2.unop ≫ ψ.down ≫ F.map f.1)` and
`ULift.up (G.map f.2.unop ≫ ψ.down ≫ f.1)`. These are Renard's
`R_F(f,g)(ψ) = F(f) ∘ ψ ∘ g` and `L_G(f,g)(ψ) = f ∘ ψ ∘ G(g)`.

Renard's initial `θ_{Y,X}` goes from `Hom_B(Y, F(X))` to `Hom_A(G(Y), X)`;
it is `theta.hom` here. Mathlib's
`adj.homEquiv Y X : (G.obj Y ⟶ X) ≃ (Y ⟶ F.obj X)` has the opposite
direction, as does the map that A.V.2 again calls `θ`. So `theta.hom`
corresponds to `(adj.homEquiv Y X).symm` and `theta.inv` to
`adj.homEquiv Y X`. These are exactly the two published component equations.

The source's `L_G` arrow display prints `Hom_B` where the arrows belong to
`A`, and its counit paragraph prints the identity at `F(Y)` where the bound
object is `X`. The published foundation uses `Hom_A`, as typing requires. The
counit built below is the image of the identity at `F(X)`, the type-correct
reading. The statement pair records these corrections and the older errata,
and this proof does not change them.

## Implemented proof

The module imports only the unchanged statement module. It defines a natural
isomorphism from a native adjunction and a native adjunction from a supplied
isomorphism. It proves their component formulas, one theorem per published
component, and the aggregate.

### The isomorphism of a native adjunction

`homIsoOfAdjunction adj : rightHomBifunctor F ≅ leftHomBifunctor G` is built
directly as an `Iso` of functors. At an object `p` of `A × Bᵒᵖ`, its forward
component is the function `ψ ↦ ULift.up ((adj.homEquiv (unop p.2) p.1).symm
ψ.down)`. Its inverse component is
`ψ ↦ ULift.up (adj.homEquiv (unop p.2) p.1 ψ.down)`.

Naturality of the forward map is checked on an arbitrary arrow `f : p ⟶ q`
of the product category, so both variables move at once. After extensionality
and removing the lift, the goal is

```text
(adj.homEquiv (unop q.2) q.1).symm (f.2.unop ≫ ψ.down ≫ F.map f.1)
  = G.map f.2.unop ≫ (adj.homEquiv (unop p.2) p.1).symm ψ.down ≫ f.1.
```

Mathlib's `Adjunction.homEquiv_naturality_left_symm` moves the leading
`f.2.unop` out as `G.map f.2.unop`. Then
`Adjunction.homEquiv_naturality_right_symm` moves the trailing `F.map f.1`
out as `f.1`. The inverse map is natural in the same way, by
`Adjunction.homEquiv_naturality_left` and
`Adjunction.homEquiv_naturality_right`. The two inverse laws `hom ≫ inv = 𝟙`
and `inv ≫ hom = 𝟙` are checked at each object and element. They are
`Equiv.apply_symm_apply` and `Equiv.symm_apply_apply` for
`adj.homEquiv (unop p.2) p.1` under the lift.

`homIsoOfAdjunction_hom_app_down` and `homIsoOfAdjunction_inv_app_down`
record the component formulas at `(X, op Y)`. Both hold by `rfl`, because the
components are defined by these formulas.

### The adjunction of a supplied isomorphism

Let `theta : rightHomBifunctor F ≅ leftHomBifunctor G` be arbitrary.
`coreHomEquivOfHomIso theta` is Mathlib's `Adjunction.CoreHomEquiv G F`: a
family of equivalences
`(G.obj Y ⟶ X) ≃ (Y ⟶ F.obj X)`, natural in `Y` and in `X`. Its forward map
is `h ↦ (theta.inv.app (X, op Y) (ULift.up h)).down`. Its inverse is
`k ↦ (theta.hom.app (X, op Y) (ULift.up k)).down`. So the unlifted maps are
read off the two components of the supplied `theta` itself.

The two inverse identities come from the inverse laws of `theta` at the
object `(X, op Y)`. `theta.inv_hom_id_app (X, op Y)` is applied to the
element `ULift.up h` with `types_congr_hom`, and `theta.hom_inv_id_app` to
`ULift.up k`. Then `ULift.down` is applied to both sides.

The two naturality fields of `CoreHomEquiv` are the naturality of `theta`
at special arrows of the product category:

- For `f : Y' ⟶ Y` and `g : Y ⟶ F.obj X`, the field requires
  `(theta.hom.app (X, op Y') (ULift.up (f ≫ g))).down =
  G.map f ≫ (theta.hom.app (X, op Y) (ULift.up g)).down`. The proof
  evaluates `theta.hom.naturality` at the arrow
  `(𝟙 X, f.op) : (X, op Y) ⟶ (X, op Y')` on the element `ULift.up g`. By the
  definitions of the two bifunctors, this gives the same equation with
  `f ≫ g ≫ F.map (𝟙 X)` on the left and a trailing `≫ 𝟙 X` on the right.
  `Functor.map_id` and `Category.comp_id` remove the identities.
- For `f : G.obj Y ⟶ X` and `g : X ⟶ X'`, the field requires
  `(theta.inv.app (X', op Y) (ULift.up (f ≫ g))).down =
  (theta.inv.app (X, op Y) (ULift.up f)).down ≫ F.map g`. The proof
  evaluates `theta.inv.naturality` at `(g, 𝟙 (op Y)) : (X, op Y) ⟶ (X', op Y)`
  on `ULift.up f`, and removes `G.map (𝟙 Y)` and `𝟙 Y` with `Functor.map_id`
  and `Category.id_comp`.

Mathlib derives the other two naturality forms from these. Naturality of
`theta` at arbitrary product arrows is supplied by the actual isomorphism;
these two families of arrows are the only instances the construction needs.

`adjunctionOfHomIso theta` is `Adjunction.mkOfHomEquiv (coreHomEquivOfHomIso
theta)`. Mathlib's construction takes the unit at `Y` to be the image of
`𝟙 (G.obj Y)` and the counit at `X` the inverse image of `𝟙 (F.obj X)`. This
is the A.V.2 recipe, with the counit at the type-correct object. Mathlib
derives the triangle identities from the Hom equivalence and its naturality.
Mathlib's lemma `Adjunction.mkOfHomEquiv_homEquiv` states that the Hom
equivalence of the resulting adjunction is exactly the supplied
`CoreHomEquiv` equivalence. `adjunctionOfHomIso_homEquiv_symm_apply` and
`adjunctionOfHomIso_homEquiv_apply` rewrite with this lemma and close by
`rfl`. They give

```text
((adjunctionOfHomIso theta).homEquiv Y X).symm k
  = (theta.hom.app (X, op Y) (ULift.up k)).down,
(adjunctionOfHomIso theta).homEquiv Y X h
  = (theta.inv.app (X, op Y) (ULift.up h)).down.
```

### 1. `nativeToHomStatement`

For a supplied `adj : G ⊣ F` the witness is `homIsoOfAdjunction adj`. The
two exact equations are `homIsoOfAdjunction_hom_app_down adj` and
`homIsoOfAdjunction_inv_app_down adj`.

### 2. `homToNativeStatement`

For a supplied `theta` the witness is `adjunctionOfHomIso theta`. The two
exact equations are the symmetric forms of
`adjunctionOfHomIso_homEquiv_symm_apply theta` and
`adjunctionOfHomIso_homEquiv_apply theta`. They concern the same `theta`
that was supplied, at both its hom and inverse components. No adjunction is
assumed: the only adjunction is the one constructed.

### 3. `homAdjunctionIffNativeStatement`

The proof unfolds `HomAdjunction G F` to
`Nonempty (rightHomBifunctor F ≅ leftHomBifunctor G)`. The forward direction
sends a witness `theta` to `adjunctionOfHomIso theta`, and the reverse sends
`adj` to `homIsoOfAdjunction adj`.

### The aggregate

`homAdjunctionComparisonStatements` is the anonymous-constructor triple of
the three component theorems in the published order. Lean's flattening of
the anonymous constructor matches the right-associated conjunction.

## Generality and checks

The proof adds no assumption on the categories or functors. There are no
smallness, universe-equality, nonemptiness, additivity, abelian or finiteness
hypotheses, and no replacement interface for the published bifunctors. The
four universe levels stay independent. The helper declarations use the same
implicit categories and functors and add nothing to the target.

The complete-declaration inspection of `homAdjunctionComparisonStatements`
reports kind `theorem`, level parameters `[vA, uA, vB, uB]` and only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. The module
compiles with no errors or warnings. The statement pair and its imports are
unchanged.

## Scope

This proves the Hom-bifunctor/native adjunction comparison aggregate only.
The native unit–counit family has its own published proof. The A.V.1
representability criterion and the uniqueness of adjoints, the A.V.2
preservation theorem, scalar extension and its source example are separate
obligations. This proof does not complete A.V, Appendix A or the whole book.
