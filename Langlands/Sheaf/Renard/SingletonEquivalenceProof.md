# Proof: Renard III.3.2 singleton sheaves and smooth representations

Worker 138 implemented this proof for Task 5595
(`6f50ec94-5361-4b14-9369-8f548b0931d5`). The entry theorem is
`Langlands.Sheaf.Renard.SingletonEquivalence.statement :
Langlands.Sheaf.Renard.SingletonEquivalence.Statement`. It proves the published
closed proposition in `Langlands/Sheaf/Renard/SingletonEquivalenceStatement.lean`,
which is unchanged and imported as is.

The statement covers every group `G : Type uG` with a topology and
`IsTopologicalGroup G` that satisfies `Langlands.Topology.IsLocallyProfinite G`.
For each such group it asserts six things:

- the published unit `SectionActions.SingletonSheaves.unit G` is an isomorphism;
- the published counit `SectionActions.SingletonSheaves.counit G` is an isomorphism;
- the triangle law for `SectionActions.gammaC G PUnit` holds;
- the triangle law for `SectionActions.SingletonSheaves.functor G` holds;
- `gammaC G PUnit` is an equivalence;
- `SingletonSheaves.functor G` is an equivalence.

The proof adds no premise. It never uses the topological-group or locally profinite
hypotheses: those hold in Renard's setting, and the statement keeps them, but
the singleton argument needs only that the space has one point and that the
action sheaves satisfy the sheaf condition. The functors and natural transformations
are the published ones. No substitute category or comparison map is introduced.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, III.3.2, the opening category paragraph and the compact-section
functor, printed p.84 / PDF p.90. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. PDF p.90
was read for this proof. After defining the category `C^∞_{X,G}-Mod`, Renard
writes "Par exemple, si X = {x} est un singleton, alors C^∞_{X,G}-Mod est
simplement M(G)", gives no proof, and then introduces the compact-section functor
`Γ_c : C^∞_{X,G}-Mod → M(G)`. The source map is
`notes/renard/iii3-sheaf-sections.md`. The proof below is a direct argument on
the published Lean objects.

## Implemented proof

The file `SingletonEquivalenceProof.lean` works in the namespace
`Langlands.Sheaf.Renard.SingletonEquivalence`.

### Arrows to the whole singleton

`toTop U` is the published label-one inclusion
`ActionOpens.inclusionHom le_top : U ⟶ ActionOpens.top`. Suppose `y` is a point of
`U`. The published arrow `SingletonSheaves.topArrow G U y : top ⟶ U` also has label
`1`. Arrows of the transport category are equal when their labels are equal
(`ActionOpens.Hom.ext`), and composition multiplies labels. So:

- `toTop_comp_topArrow`: `toTop U ≫ topArrow G U y = 𝟙 U`;
- `topArrow_comp_toTop`: `topArrow G U y ≫ toTop U = 𝟙 top`.

Apply the contravariant sheaf `F.obj` to these equations. This gives
`restrict_extend`: the original extension `F.obj.map (topArrow G U y).op`, followed
by restriction `F.obj.map (toTop U).op`, is the identity on `F(U)`. It also gives
`extend_restrict`: restriction followed by extension is the identity on global
sections. So over a nonempty open, extension along `topArrow` is a linear bijection.

### Sections over the empty open

`subsingleton_of_empty` applies Mathlib's `TopCat.Sheaf.isTerminalOfEqEmpty` to the
ordinary sheaf `(toSheaf G PUnit (ModuleCat ℂ)).obj F`. That ordinary sheaf is the
published underlying sheaf of the action sheaf. Its value on `U.openSet = ⊥` is
definitionally `F.obj.obj (op U)`. A terminal module has `𝟙 = 0` as endomorphisms,
so every section is zero.

### The unit is invertible

`toCoefficientSection_bijective` shows that the published component
`SingletonSheaves.toCoefficientSection F U` is bijective for every action sheaf `F`
and every transport object `U`. There are two cases.

- **`U` has a point `y`.** Every point of `U` equals `y`, since the space is a
  singleton. For injectivity, evaluate both coefficient functions at `y`. This
  gives equal extensions `F.obj.map (topArrow G U y).op s` and
  `F.obj.map (topArrow G U y).op t`; then `restrict_extend` gives `s = t`. For
  surjectivity, take a locally constant compact-section function `f` on `U`. The
  section `F.obj.map (toTop U).op (f y).val` is a preimage by `extend_restrict`,
  since the only point of `U` is `y`.
- **`U` is empty.** `F(U)` is a subsingleton by `subsingleton_of_empty`. Locally
  constant functions on the empty open form a subsingleton too. So the map is
  bijective.

`isIso_unit_app` turns this into invertibility of `(unit G).app F`. Each
`ModuleCat` component is an isomorphism by `ConcreteCategory.isIso_iff_bijective`.
The natural transformation of transport presheaves is then an isomorphism by
`NatIso.isIso_of_isIso_app`. The two full-subcategory inclusions,
`sheafProperty` and `smoothActionProperty`, are fully faithful, so
`Functor.FullyFaithful.isIso_of_isIso_map` lifts the isomorphism to
`TopologicalSheaf` and then to `SmoothActionSheaf`. `isIso_unit` concludes
componentwise by `NatIso.isIso_of_isIso_app`.

### The counit is invertible

`constSection A` sends a vector `a` of a smooth representation `A` to the constant
locally constant section on `⊤ : Opens PUnit`. Every subset of `PUnit` is finite,
so this section has compact support. It is a compact section of the published
coefficient sheaf `(SingletonSheaves.functor G).obj A`. The map intertwines the
group actions. The compact-section action at `g` reads the coefficient at
`g⁻¹ • pt` and applies `A.representation (g⁻¹)⁻¹`, which `inv_inv` turns into
`A.representation g`.

`isIso_counit_app` uses `SmoothRep.ofHom (constSection A)` as the explicit inverse
of the literal evaluation `(counit G).app A`. Evaluating a constant section gives
back its value. In the other direction, a locally constant section on the
one-point open equals the constant section at its unique value. Both identities
hold definitionally, because every element of `PUnit` is definitionally
`PUnit.unit`. `isIso_counit` concludes componentwise.

### Triangle laws

- `triangle_gammaC` is the first triangle law. Take an action sheaf `F` and an
  original compact section `s`. Apply `gammaC.map (unit.app F)` and then the counit;
  this evaluates the coefficient function at the point. The result is
  `F.obj.obj.map (topArrow G top pt).op s`. That arrow has label `1`, so it equals
  `𝟙 top`, and the result is `s`.
- `triangle_functor` is the second triangle law. Take a representation `A`, an open
  `U`, a section `s` and a point `y`. The unit followed by the pointwise counit
  gives `A.representation (1⁻¹) (s ⟨1 • pt, _⟩)`: this is the published pullback
  along the label-one arrow `topArrow`. It reduces to `s y` by `inv_one`, `map_one`
  and the fact that the space has one point.

### Equivalences and the entry theorem

`equivalence G` is `CategoryTheory.Equivalence.mk'` applied to the exact functors
`gammaC G PUnit` and `SingletonSheaves.functor G`, with unit isomorphism
`asIso (unit G)`, counit isomorphism `asIso (counit G)` and triangle law
`triangle_gammaC`. The entry theorem `statement` takes the group and its
hypotheses. It then returns the two invertibility instances, the two triangle
laws, and `Equivalence.isEquivalence_functor` and `isEquivalence_inverse` of this
equivalence. Their functors are exactly `gammaC G PUnit` and
`SingletonSheaves.functor G`.

## Checks

The development check compiled the module with no errors or warnings. Inspection
of `Langlands.Sheaf.Renard.SingletonEquivalence.statement` reported only the
axioms `propext`, `Classical.choice` and `Quot.sound`. The file uses no `sorry`
and declares no axiom. It uses the same `backward.defeqAttrib.useBackward` and
`backward.isDefEq.respectTransparency` options as the imported
`SingletonSheaves` module, and disables the unused-section-variable linter.
