# Renard A.V.2: proofs of the unit–counit statements

Worker 1172 proves the published closed proposition
`Langlands.Renard.UnitCounit.UnitCounitStatements.{vA,uA,vB,uB}`,
imported from `Langlands.CategoryTheory.Renard.UnitCounitStatements`.
The final theorem is `Langlands.Renard.UnitCounit.unitCounitStatements`.
Its type is exactly the closed aggregate at the four independent universe
levels `vA,uA,vB,uB`. It has no extra assumptions or parameters.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The assertions are in A.V.2, printed p.259 / one-based PDF265. The Hom
functors `R_F`, `L_G` and the isomorphism `θ` of the A.V.1 definition are on
printed p.258 / PDF264. Both pages were read for this proof. Renard gives no
written proofs of these assertions: he states the triangle identities, says
that naturality of `θ` and `σ` follows easily from naturality of `η` and `ε`,
and that the triangles make `θ` and `σ` inverse to each other. The proofs below
are the standard arguments.

## Conventions

The statement companion explains the source-to-Lean formulation. Renard's
`G : B → A` is the left adjoint and `F : A → B` the right adjoint, so the
native adjunction is Mathlib's `adj : G ⊣ F`. The unit has type
`𝟭 B ⟶ G ⋙ F` and the counit `F ⋙ G ⟶ 𝟭 A`; Renard's `FG(Y)` is Lean's
`F.obj (G.obj Y)`. In Lean `f ≫ g` means `g ∘ f`. The equivalence
`adj.homEquiv Y X` goes from `Hom_A(G(Y), X)` to `Hom_B(Y, F(X))`. This is the
direction of the map `θ_{Y,X}` in the converse passage on PDF265. The
isomorphism of the A.V.1 definition on PDF264 has the opposite direction and
corresponds to the inverse equivalence.

The source's counit paragraph prints the identity at `F(Y)`. The statement
uses the identity at `F(X)`, as its type requires; the proof keeps that
statement unchanged.

Mathlib's `Adjunction` structure stores the unit, the counit and the two
triangle identities as fields. Its `homEquiv` is defined from them, by
`h ↦ unit.app Y ≫ F.map h` and `k ↦ G.map k ≫ counit.app X`. The first four
components therefore record facts about this native structure. They do not
compare it with a separately given isomorphism of Hom bifunctors.

## Implemented proof

The module imports only the unchanged statement module. It contains one
theorem per component, named after the component in lower camel case, and the
aggregate theorem. The first four components introduce `A`, `B`, `G`, `F`
and an actual `adj : G ⊣ F`. The last three introduce `A`, `B`, `G`, `F` and
arbitrary actual natural transformations `η : 𝟭 B ⟶ G ⋙ F` and
`ε : F ⋙ G ⟶ 𝟭 A`.

### 1. Unit and counit at identities

`unitCounitAtIdentitiesStatement` uses Mathlib's `Adjunction.homEquiv_id`
for the unit and `Adjunction.homEquiv_symm_id` for the counit, read
backwards. By the defining formulas, `homEquiv` sends `𝟙 (G.obj Y)` to
`adj.unit.app Y ≫ F.map (𝟙 (G.obj Y))`. Its inverse sends `𝟙 (F.obj X)` to
`G.map (𝟙 (F.obj X)) ≫ adj.counit.app X`. Functoriality and the identity laws
reduce these to `adj.unit.app Y` and `adj.counit.app X`.

### 2. Naturality of the unit and counit

`unitCounitNaturalityStatement` applies the `naturality` fields of the
natural transformations `adj.unit` and `adj.counit`. For `f : Y ⟶ Y'`, the
field `adj.unit.naturality f` states `(𝟭 B).map f ≫ adj.unit.app Y' =
adj.unit.app Y ≫ (G ⋙ F).map f`. This is the published equation up to
unfolding the identity and composite functors. The counit case
`adj.counit.naturality g` is the same for `g : X ⟶ X'`.

### 3. Triangle identities

`triangleIdentitiesStatement` returns the two triangle fields of `adj`. The
first published identity, (A.V.2.1), is `adj.right_triangle_components X`:
`adj.unit.app (F.obj X) ≫ F.map (adj.counit.app X) = 𝟙 (F.obj X)`. The
second, (A.V.2.2), is `adj.left_triangle_components Y`:
`G.map (adj.unit.app Y) ≫ adj.counit.app (G.obj Y) = 𝟙 (G.obj Y)`. Mathlib's
left triangle is the identity on the left adjoint `G`, and its right triangle
the identity on the right adjoint `F`; so the right triangle comes first here.

### 4. Hom equivalence formulas

`homEquivFormulasStatement` applies Mathlib's `Adjunction.homEquiv_unit` and
`Adjunction.homEquiv_counit`. These lemmas are the defining formulas of
`homEquiv` and its inverse:
`adj.homEquiv Y X h = adj.unit.app Y ≫ F.map h` and
`(adj.homEquiv Y X).symm k = G.map k ≫ adj.counit.app X`.

### 5. Naturality of the raw Hom maps

`homMapNaturalityStatement` uses only the naturality of `η` and `ε`; no
triangle identity is available or used. Let `f : Y' ⟶ Y` and `g : X ⟶ X'`.

For the first map and `h : G.obj Y ⟶ X`, the local fact
`hη : η.app Y' ≫ F.map (G.map f) = f ≫ η.app Y` is the symmetric form of
`η.naturality f`. The proof rewrites with `Functor.map_comp` and
`Category.assoc`. Both sides become right-associated composites, and the
`reassoc_of%` form of `hη` rewrites a leading
`η.app Y' ≫ F.map (G.map f)` to `f ≫ η.app Y`. Both sides then equal
`f ≫ η.app Y ≫ F.map h ≫ F.map g`.

For the second map and `k : Y ⟶ F.obj X`, the local fact
`hε : G.map (F.map g) ≫ ε.app X' = ε.app X ≫ g` is `ε.naturality g`. The
same simplification with `Functor.map_comp`, `Category.assoc` and `hε` turns
both sides into `G.map f ≫ G.map k ≫ ε.app X ≫ g`.

These two equations are Renard's claim on PDF265 that `θ` and `σ` are natural
transformations from `L_G` to `R_F` and from `R_F` to `L_G`. Each is written
out on arbitrary arrows in both variables at once.

### 6. The raw Hom maps are mutually inverse

`homMapInverseIdentitiesStatement` introduces `η`, `ε` and the two triangle
hypotheses `hright` (A.V.2.1) and `hleft` (A.V.2.2). Each identity uses one
triangle and the naturality of one transformation.

For `h : G.obj Y ⟶ X`, the local fact
`hε : G.map (F.map h) ≫ ε.app X = ε.app (G.obj Y) ≫ h` is `ε.naturality h`.
The proof rewrites the left side as follows:

```text
G.map (η.app Y ≫ F.map h) ≫ ε.app X
  = G.map (η.app Y) ≫ G.map (F.map h) ≫ ε.app X      (G.map_comp, assoc)
  = G.map (η.app Y) ≫ ε.app (G.obj Y) ≫ h            (hε)
  = (G.map (η.app Y) ≫ ε.app (G.obj Y)) ≫ h          (assoc)
  = 𝟙 (G.obj Y) ≫ h                                  (hleft Y)
  = h                                                (Category.id_comp)
```

For `k : Y ⟶ F.obj X`, the local fact
`hη : η.app Y ≫ F.map (G.map k) = k ≫ η.app (F.obj X)` is the symmetric form
of `η.naturality k`. Dually:

```text
η.app Y ≫ F.map (G.map k ≫ ε.app X)
  = (η.app Y ≫ F.map (G.map k)) ≫ F.map (ε.app X)    (F.map_comp, assoc)
  = (k ≫ η.app (F.obj X)) ≫ F.map (ε.app X)          (hη)
  = k ≫ η.app (F.obj X) ≫ F.map (ε.app X)            (assoc)
  = k ≫ 𝟙 (F.obj X)                                  (hright X)
  = k                                                (Category.comp_id)
```

The last step of each chain is closed by `exact Category.id_comp h` and
`exact Category.comp_id k`, which check the identity law up to definitional
unfolding of the identity and composite functors.

### 7. Adjunction from the supplied unit and counit

`adjunctionFromUnitCounitStatement` builds the Mathlib structure directly:

```lean
{ unit := η
  counit := ε
  left_triangle_components := hleft
  right_triangle_components := hright }
```

The triangle fields are exactly the hypotheses (A.V.2.2) and (A.V.2.1); their
field types agree with the hypotheses up to unfolding the identity and
composite functors. The witness's unit and counit are `η` and `ε` by
construction, so both equations `adj.unit = η` and `adj.counit = ε` hold by
`rfl`. The supplied transformations are kept exactly. This is Renard's
adjunction quadruple `(F, G, ε, η)` in Mathlib's native structure.

### The aggregate

`unitCounitStatements` is the anonymous-constructor tuple of the seven
component theorems in the published order. The right-associated conjunction
of the target is matched by Lean's flattening of the anonymous constructor.

## Generality and checks

The proof adds no assumption on the categories, functors or transformations.
The four universe levels are independent. In components 5 to 7 no adjunction
is assumed in advance: component 5 holds for arbitrary `η` and `ε`, and
components 6 and 7 use exactly the two published triangles.

The complete-declaration inspection of `unitCounitStatements` reports kind
`theorem`, level parameters `[vA, uA, vB, uB]` and only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. The module compiles with no
errors or warnings. The statement pair and its import are unchanged.

## Scope

This proves the native unit–counit aggregate only. The comparison from
Renard's supplied natural isomorphism between the Hom bifunctors `R_F` and
`L_G` to the native adjunction remains a separate obligation, over the
published Hom foundation. The A.V.1 representability criterion and the
uniqueness of adjoints, the A.V.2 preservation theorem and the
scalar-extension example are also separate. This proof does not complete A.V,
Appendix A or the whole book.
