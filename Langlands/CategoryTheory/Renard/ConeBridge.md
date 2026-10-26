# Renard A.IV.1–A.IV.2: corrected cone and constant-functor bridge

Authors: Worker 610 (Lean implementation and source correspondence) and Worker 6
(the mathematical diagnosis and requested counterexample, reused from the task
and [Appendix A source audit](../../../notes/renard/appendix-a-corrections.md)).

This is one definition unit for the general cone and cocone interfaces. All
declarations below belong to `Langlands.CategoryTheory.Renard` in
`Langlands.CategoryTheory.Renard.ConeBridge`. Categorical foundations, universal
witnesses and standard equivalences are reused from Mathlib; the additional
proofs are short intrinsic laws of these definitions.

## Original sources and corrections

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.IV.1–A.IV.2, printed
pages 256–257 / PDF pages 262–263. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 610 read both original pages and visually inspected their formulas and
arrows.

The supplementary author errata for the 2010 edition are registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
Their appendix correction list on PDF pages 18–19 was read. It contains no repair
of the constant-transformation assertion discussed here. This observation is
limited to that list; the errata are not a replacement edition of the governing
2026 text.

There are three repairs to distinguish.

1. The first paragraph of A.IV.1 identifies transformations between constant
   functors with morphisms between their values under the assumption that the
   index category is nonempty. This is false for a disconnected index. In the
   discrete category on two objects, a transformation from constant `PUnit` to
   constant `Bool` may have the two different components constantly `false` and
   constantly `true`. Connectedness suffices for the auxiliary Hom equivalence.
   Nonemptiness alone still supplies faithfulness.
2. The limit paragraph's parenthetical arrow on printed page 256 / PDF page 262
   is reversed. The map inducing `ΔY ⟶ ΔX` must have direction `Y ⟶ X`.
   The concrete unique factorization immediately following (A.IV.1.2) already
   has this correct direction. We retain that concrete formula.
3. The first paragraph of A.IV.2 on printed page 257 / PDF page 263 reverses
   both prose arrows. Its displayed factorization `D ⟶ ΔX ⟶ ΔY` requires
   `ΔX ⟶ ΔY` induced by `X ⟶ Y`.

For arbitrary indices, universal factorization is quantified over morphisms
between the explicit vertices. It cannot be replaced by factorization through
arbitrary transformations between constant functors. The counterexample refutes
the source's preliminary claim; it does not refute ordinary limits or colimits.
No connectedness or nonemptiness hypothesis is imposed on any general cone,
cocone, limit or colimit interface in this module.

## Diagonal functor and corrected auxiliary correspondence

Write `J : Type uJ`, `[Category.{vJ} J]`, `C : Type uC` and
`[Category.{vC} C]`. The four universe parameters are independent. The source's
`I`, `𝒞`, `Δ` and diagram `D` correspond to `J`, `C`, `diagonal J C` and
`D : J ⥤ C`, respectively.

| Lean name | Meaning and source correspondence |
| --- | --- |
| `diagonal` | `CategoryTheory.Functor.const J : C ⥤ (J ⥤ C)`, the first paragraph's `Δ`. |
| `diagonal_obj_obj`, `diagonal_obj_map` | Constant value `X` on each object and identity `𝟙 X` on each index morphism. |
| `diagonal_map_app` | The transformation induced by `f : X ⟶ Y` has component `f` at every index. |
| `diagonal_faithful` | Reuses Mathlib's faithful instance under `[Nonempty J]`. |
| `diagonal_full` | Reuses Mathlib's full instance under `[IsConnected J]`. |
| `connectedConstantHomEquiv` | The corrected equivalence `(X ⟶ Y) ≃ (ΔX ⟶ ΔY)` under `[IsConnected J]`, via `Functor.FullyFaithful.ofFullyFaithful` and `.homEquiv`. |
| `connectedConstantHomEquiv_apply_app`, `connectedConstantHomEquiv_symm_eq_app` | Forward components are the original map; the inverse recovers any component. |
| `constant_components_eq` | Reuses `CategoryTheory.nat_trans_from_is_connected`: on a preconnected index every two components agree. |

`IsPreconnected` suffices for equality of components; `IsConnected` also gives
nonemptiness, needed to recover a map from a transformation. These are corrected
auxiliary assertions derived from naturality, not results attributed to the
book with its original nonempty hypothesis. The three action formulas are
definitional equalities; inverse evaluation follows by applying
`NatTrans.congr_app` to the equivalence's inverse law.

## Concrete universal properties

The objects `Cone D` and `Cocone D` are Mathlib's actual structures. A cone
stores `t.pt : C` and `t.π : Δ(t.pt) ⟶ D`; a cocone stores `t.pt : C` and
`t.ι : D ⟶ Δ(t.pt)`. Their naturality is precisely the compatibility of the
legs in (A.IV.1.2), and its dual.

`ConeUniversal t : Prop` is the concrete property after (A.IV.1.2):

```lean
∀ s : Cone D, ∃! f : s.pt ⟶ t.pt,
  ∀ j : J, f ≫ t.π.app j = s.π.app j
```

`CoconeUniversal t : Prop` is the dual property required by the correctly
directed displayed factorization in A.IV.2:

```lean
∀ s : Cocone D, ∃! f : t.pt ⟶ s.pt,
  ∀ j : J, t.ι.app j ≫ f = s.ι.app j
```

| Lean name | Implementation and meaning |
| --- | --- |
| `isLimitOfConeUniversal`, `isColimitOfCoconeUniversal` | Construct actual `IsLimit t` / `IsColimit t` data directly using Mathlib `ofExistsUnique`. |
| `coneUniversal_of_isLimit`, `coconeUniversal_of_isColimit` | Extract the componentwise property using Mathlib `existsUnique`. |
| `coneUniversal_iff_nonempty_isLimit` | `ConeUniversal t ↔ Nonempty (IsLimit t)`. |
| `coconeUniversal_iff_nonempty_isColimit` | `CoconeUniversal t ↔ Nonempty (IsColimit t)`. |

`IsLimit` and `IsColimit` carry factorization data and are not themselves
Prop-valued predicates. `Nonempty` expresses their existence as a proposition.
These equivalences construct and recover the factorization witnesses. They
introduce no assumed certificate or separate existence hypothesis. The
noncomputable section permits the choice used by `ofExistsUnique`.

## Hom equivalences and naturality

For a supplied universal witness, the following aliases reuse Mathlib's actual
equivalences. They implement (A.IV.1.1) on printed page 256 / PDF page 262 and
its categorical dual from A.IV.2:

```text
limitHomEquiv h Y  : (Y ⟶ t.pt) ≃ (ΔY ⟶ D)
colimitHomEquiv h Y : (t.pt ⟶ Y) ≃ (D ⟶ ΔY)
```

Here `h : IsLimit t` or `h : IsColimit t`, respectively. The forward maps have
components `f ≫ t.π.app j` and `t.ι.app j ≫ f`; this is recorded by
`limitHomEquiv_apply_app` and `colimitHomEquiv_apply_app`. The inverse maps
satisfy the corresponding factorization equations in
`limitHomEquiv_symm_app` and `colimitHomEquiv_symm_app`.

`limitHomEquiv_naturality` says that precomposing `f : Y ⟶ t.pt` by
`g : Z ⟶ Y` corresponds to precomposing its transformation by `Δg`.
`colimitHomEquiv_naturality` says that postcomposing `f : t.pt ⟶ Y`
by `g : Y ⟶ Z` corresponds to postcomposing its transformation by `Δg`.
Both proofs apply transformation extensionality and associativity.
`limitHomEquiv_symm_naturality` and `colimitHomEquiv_symm_naturality`
reuse the respective Mathlib `homEquiv_symm_naturality` laws.

The natural isomorphisms reuse Mathlib `IsLimit.natIso` and
`IsColimit.natIso` without suppressing the universe lift:

```lean
limitNatIso h :
  yoneda.obj t.pt ⋙ uliftFunctor.{uJ} ≅ D.cones
colimitNatIso h :
  coyoneda.obj (Opposite.op t.pt) ⋙ uliftFunctor.{uJ} ≅ D.cocones
```

The cone and cocone functors take values in `Type (max uJ vC)`. The Hom
functors have values in `Type vC`, so `uliftFunctor.{uJ}` is retained.
`limitNatIso_hom_app` and `colimitNatIso_hom_app` give the same component
formulas with `f.down` for the lifted Hom element. No equality of object and
morphism universes or size restriction on `J` is assumed.

## Canonical isomorphisms

The uniqueness remark following the limit definition on printed page 256 /
PDF page 262, and its dual, are implemented by the existing canonical maps:

| Lean name | Mathlib construction |
| --- | --- |
| `limitConeIso`, `colimitCoconeIso` | `IsLimit.uniqueUpToIso` / `IsColimit.uniqueUpToIso`, in the actual category of cones / cocones. |
| `limitPointIso`, `colimitPointIso` | `conePointUniqueUpToIso` / `coconePointUniqueUpToIso`, on their vertices. |

The cone and cocone morphisms already carry the leg preservation equations.
For the vertex isomorphisms these equations are exposed explicitly in both
directions by `limitPointIso_hom_comp`, `limitPointIso_inv_comp`,
`comp_colimitPointIso_hom` and `comp_colimitPointIso_inv`, reusing Mathlib.
`limitPointIso_eq` and `colimitPointIso_eq` characterize the canonical
isomorphism among vertex isomorphisms whose forward maps preserve all legs.
Their proofs use universal uniqueness and `Iso.ext`. There is no claim that
arbitrary vertex isomorphisms preserve the cone or cocone structure.

## Counterexample, empty index and checked scope consumers

These declarations are derived internal examples. The two-object diagnosis
comes from Worker 6's source audit; the book does not state this counterexample.

`TwoPointIndex := Discrete Bool` and `twoPointTransformation` implement the
explicit transformation from constant `PUnit` to constant `Bool`.
`Discrete.natTrans` supplies naturality; `twoPointTransformation_app` computes
its value to the chosen Boolean index for every singleton element.
`twoPointTransformation_not_diagonal` states intrinsically that no morphism
`f : PUnit ⟶ Bool` has this image under the diagonal functor. In `Type`, such
morphisms are bundled functions. The proof evaluates a purported equality of
transformations at `false` and `true`, using `NatTrans.congr_app` and
`ConcreteCategory.congr_hom`, and obtains `false = true`.
`twoPointIndex_nonempty` records explicitly why nonemptiness does not repair
the failed assertion.

`EmptyIndex := Discrete PEmpty`.
`empty_constant_functors_eq` proves that the constant functors named by `PUnit`
and by `Bool` are equal on this empty index. Functor extensionality has no
components to check. `punit_ne_bool` proves these named vertices are distinct:
transporting the singleton's subsingleton instance to `Bool` would identify
`false` and `true`. `emptyCone X` and `emptyCocone X` instead store `X`
as their vertex over one fixed empty diagram. `emptyCone_pt`,
`emptyCocone_pt`, `emptyCone_vertices_differ` and
`emptyCocone_vertices_differ` record the retained vertices. Equality of
constant functors on an empty category does not erase a cone's or cocone's
explicit vertex field.

`singletonCone J` with `singletonConeIsLimit J` is a constant singleton
limiting cone in `Type`, for arbitrary `J`. The lift is the unique function to
`PUnit`; its laws follow from subsingleton elimination.
`emptyTypeCocone J` with `emptyTypeCoconeIsColimit J` is a constant
empty-type colimiting cocone for arbitrary `J`. The descent is the function
out of `PEmpty`; its laws follow by eliminating the empty element.
The component arrows are actual Mathlib `Type` morphisms, constructed using
`TypeCat.ofHom` notation.

`twoPoint_limit_consumer` and `twoPoint_colimit_consumer` apply the universal
property conversions on the disconnected index, in opposite directions.
`empty_limit_consumer` and `empty_colimit_consumer` do the same on the empty
index. These checked uses demonstrate that the general interfaces retain both
scopes. They are small internal examples; they do not implement the source's
general products, pullbacks, kernels or filtered colimits.

## Reuse and boundary

The implementation imports `Mathlib.CategoryTheory.IsConnected` and
`Mathlib.CategoryTheory.Limits.IsLimit`, using Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. There are no new axioms or
unfinished proofs. All laws grouped here are intrinsic to the displayed
definitions and reused universal witnesses.

This unit covers the constant functor, the corrected general definitions, Hom
correspondences and canonical uniqueness, together with the explicit diagnostic
examples. The detailed examples and existence results for products, pullbacks,
kernels, filtered colimits of abelian groups, universal-arrow and adjunction
theory, and the separate module-localization discrepancy in A.III.1 remain
outside this unit. It does not establish whole-Appendix coverage.
