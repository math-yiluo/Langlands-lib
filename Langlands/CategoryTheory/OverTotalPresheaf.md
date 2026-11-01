# The total presheaf of a presheaf on an over category

Let `C : Type u` have a category structure with morphisms in `Type v`, let
`S : C`, and let `G : (Over S)ᵒᵖ ⥤ Type w` be a presheaf. The module keeps
these three universes independent. Its namespace is
`CategoryTheory.Functor`.

For `T : C`, `G.OverTotal T` is the dependent sum

```lean
Σ t : T ⟶ S, G.obj (op (Over.mk t))
```

in `Type (max w v)`. It remembers both a structure morphism to `S` and an
element of `G` on that object of the over category. The functor
`G.overTotal : Cᵒᵖ ⥤ Type (max w v)` sends an underlying morphism
`f : T' ⟶ T` and a pair `(t, x)` to `(f ≫ t, G(f) x)`, using the actual
over-category morphism from `Over.mk (f ≫ t)` to `Over.mk t`.
`overTotal_map_fst` records the resulting structure morphism by reflexivity.

The lemmas `map_op_apply_eq_of_left_eq` through
`map_op_map_op_apply_eq` give the functorial equalities used in the
construction. Over-category morphisms with equal underlying morphisms are
equal. The functor identity and composition laws then identify their induced
maps, including composites of two or three maps. `OverTotal.ext'` combines
equality of the structure morphisms with equality of the fibre elements after
transport by the identity underlying morphism. The identity and composition
proofs for `overTotal` apply this extensionality principle and those
functorial equalities.

For `T : Over S`, `OverTotal.toFibre T b hb` turns a total element `b` whose
first component equals `T.hom` into an element of `G.obj (op T)`. It applies
`G` to the over-category morphism with underlying identity. Conversely,
`OverTotal.ofFibre T x` pairs `T.hom` with the element transported to
`Over.mk T.hom`. `toFibre_ofFibre` and `ofFibre_toFibre` prove the inverse
identities; the latter has the explicit hypothesis `b.1 = T.hom`.
`toFibre_congr` gives compatibility with equality of total elements, and
`toFibre_naturality` gives compatibility with an actual morphism `T ⟶ T'`
in `Over S`. The proofs use equality of the underlying identity/composite
morphisms and the functorial equalities above.

Now suppose `e : G.overTotal.RepresentableBy Y` is supplied. The definition
`e.overTotalBase : Y ⟶ S` takes the first component of the total element
`e.homEquiv (𝟙 Y)`. Naturality of this representing equivalence gives

```lean
(e.homEquiv k).1 = k ≫ e.overTotalBase
```

for every `k : T ⟶ Y`; this is `overTotal_homEquiv_fst`.

`e.ofOverTotal` constructs
`G.RepresentableBy (Over.mk e.overTotalBase)`. A morphism from `T : Over S`
to this representing object is sent, by `e.homEquiv` on its underlying
morphism, to a total element. The displayed identity and the over-category
commutativity condition show that its first component is `T.hom`, so
`toFibre` gives the desired element of `G`. In the inverse direction,
`ofFibre` gives a total element and `e.homEquiv.symm` gives the underlying
morphism to `Y`. The same displayed identity proves it is over `S`.
Injectivity of `e.homEquiv` and the two fibre identities prove that these
maps are inverse. Finally, `homEquiv_comp` combines the naturality of
`e.homEquiv` with `toFibre_congr` and `toFibre_naturality`. Thus the output
is a natural representing equivalence on the full over category.

This construction is conditional on a supplied representation of the total
presheaf. It constructs the structure morphism on that supplied representing
object. In the CM representability task it provides a categorical step after
the geometric representing object and its equivalence have been obtained;
those existence and comparison obligations remain open.

## Source and adaptations

The complete source is `Definitions/Def_CategoryTheory_OverTotalPresheaf.lean`,
lines 1–141, at Anthropic FLT commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, registered as
`anthropic-flt-complete-lean-source-6e837e75`. The registered folder SHA-256 is
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`;
the individual original file SHA-256 is
`89217fe203e86bb8ba406e6d343b1d42aa4e5b212817efc4eae1ee704e0c54c2`.
The definitions and conclusions retain the original names, parameters and
universe levels. This port adds an attribution header, replaces `import
Mathlib` with the over-category and Yoneda imports, explicitly types the
underlying equalities in five proof steps, and changes two rewrites in
`ofOverTotal` from `rw` to `erw` for definitional reduction in the current
Mathlib. The implemented proof follows the source construction described
above. It adds no mathematical hypotheses.

The source distribution is Copyright 2026 Anthropic, PBC, licensed under the
Apache License 2.0. The existing `licenses/Anthropic-FLT/LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are byte-identical to the pinned source distribution and
retain its full notices. The upstream attribution file has no entry for this
source file. Worker 344 made the adaptations listed above. Mathlib is used
through the project's pinned environment.
