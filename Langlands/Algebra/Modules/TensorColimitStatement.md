# Tensor products preserve colimit isomorphisms of module presheaves over cofiltered diagrams

The declaration `Langlands.Algebra.Modules.tensorColimitIsIsoStatement` is a
proposition definition, parameterized by a small cofiltered category `C` and a
presheaf of commutative rings `R` on `C`. It states that the sectionwise tensor
product of two morphisms of module presheaves has an invertible colimit map
whenever both morphisms do. The file supplies no proof, instance or other
assumption of this proposition.

## Exact statement

Parameters and universes:

- `C : Type u` with `[SmallCategory C]`, so objects and morphisms of `C` are in
  universe `u`, and `[IsCofiltered C]`. Hence `Cᵒᵖ` is filtered, and the
  colimits below are filtered colimits.
- `R : Cᵒᵖ ⥤ CommRingCat.{u}`, a presheaf of commutative rings whose values may
  vary with the object. Nothing makes `R` constant, and its transition maps
  need not be invertible.
- Module presheaves are objects of `PresheafOfModulesOfCommRing.{u} R`, which is
  Mathlib's abbreviation for `PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)`.
  An object `M` assigns to each `X : Cᵒᵖ` an `R(X)`-module `M(X)` with carrier
  in universe `u`. Its restriction maps are semilinear over the ring maps of `R`.

The functor used to form colimits is exactly

```lean
L := PresheafOfModules.toPresheaf.{u} (R ⋙ forget₂ CommRingCat RingCat) ⋙ colim
```

with type `PresheafOfModulesOfCommRing.{u} R ⥤ AddCommGrpCat.{u}`. The first
factor forgets each module presheaf to its underlying presheaf
`Cᵒᵖ ⥤ AddCommGrpCat.{u}` of abelian groups. A morphism goes to the family of
its additive maps on sections. The second factor is
`CategoryTheory.Limits.colim` for diagrams of shape `Cᵒᵖ` in `AddCommGrpCat.{u}`. The colimit exists
because `Cᵒᵖ` is `u`-small. Instance search selects
`AddCommGrpCat.hasColimitsOfShape` from
`Mathlib.Algebra.Category.Grp.Colimits`, which the file imports. So for
`f : M ⟶ M'`, `L.map f` is the homomorphism `colim_X M(X) ⟶ colim_X M'(X)` of
abelian groups induced by the components of `f`. Being an isomorphism in
`AddCommGrpCat` means being a bijective additive map.

The tensor product is Mathlib's sectionwise monoidal structure
`PresheafOfModulesOfCommRing.monoidalCategory`, from
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal`. For module presheaves
`M` and `N`, `(M ⊗ N)(X) = M(X) ⊗[R(X)] N(X)`, and restriction sends
`m ⊗ n` to the tensor of the restrictions of `m` and `n`. For `f : M₁ ⟶ M₂`
and `g : N₁ ⟶ N₂`, the morphism `f ⊗ₘ g : M₁ ⊗ N₁ ⟶ M₂ ⊗ N₂` has component
`f(X) ⊗ g(X)` at each `X`. There is no sheafification.

The proposition for `C` and `R` is

```lean
∀ (M₁ M₂ N₁ N₂ : PresheafOfModulesOfCommRing.{u} R) (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂),
  IsIso (L.map f) → IsIso (L.map g) → IsIso (L.map (f ⊗ₘ g))
```

In words: suppose the colimit map of `f` and the colimit map of `g` are
isomorphisms of abelian groups. Then the colimit map of `f ⊗ₘ g` is an isomorphism
`colim_X (M₁(X) ⊗[R(X)] N₁(X)) ≅ colim_X (M₂(X) ⊗[R(X)] N₂(X))`.
The statement has no flatness, finite-presentation, finite-type,
constant-ring or invertible-transition hypotheses. It does not mention
sheaves, sheafification, sites, local equivalences or any monoidal structure on
sheaves. In particular, it does not depend on
`Langlands.Scheme.Modules.tensorLocalEquivalencesIsMonoidalStatement`.

## Provenance and mathematical content

This is an internal algebraic prerequisite, not a verbatim statement from the
literature. It comes from the standard fact that tensor products commute with
filtered colimits even when the base ring varies. Write `A = colim_X R(X)` for
the colimit ring over the filtered category `Cᵒᵖ`. For a module presheaf `M`, the
abelian group `colim_X M(X)` carries a natural `A`-module structure. Then there
is a canonical isomorphism

`colim_X (M(X) ⊗[R(X)] N(X)) ≅ (colim_X M(X)) ⊗[A] (colim_X N(X))`,

natural in `M` and `N`. Under this identification, `L.map (f ⊗ₘ g)` corresponds
to the tensor product over `A` of the colimit maps of `f` and `g`. These maps are
`A`-linear and, by hypothesis, bijective, so their tensor product is bijective.
This outline explains why the proposition is expected to hold. It is not part of
the Lean statement, and a separate proof must establish the proposition.

The best-known instance is the stalk formula
for a ringed space, Stacks Project Lemma 17.16.1 (Section 17.16, tag 01CA).
It says: "There is a canonical isomorphism of
`O_{X,x}`-modules `(F ⊗_{O_X} G)_x = F_x ⊗_{O_{X,x}} G_x` functorial in `F` and
`G`". The proof is omitted in Stacks. The stalk is the filtered colimit over the
neighborhoods of `x`, with the rings `O_X(U)` varying. The present statement
isolates the corresponding morphism-level algebraic consequence for an arbitrary
small cofiltered index category and arbitrary module presheaves, before any
sheafification. The registered source is `stacks-module-tensor-products-2026-10-21`,
*Stacks Project - Tensor products of sheaves of modules (HTML snapshot
2026-10-21)*, with SHA256
`825127394e5828c3a56f5134b8823afba20547d7ba5173f624b2f9556a058e34`.
That source also contains Lemma 17.16.2 (tag 05NA), which is the provenance of
the scheme-level statement this prerequisite serves.

## Role and relevant interfaces

This prerequisite is needed by proof task
`1033dad0-ce5e-4bfd-9df3-97c690ee49bd`, which proves
`Langlands.Scheme.Modules.tensorLocalEquivalencesIsMonoidalStatement`. A
conservative family of site points reduces local equivalences to colimit
isomorphisms on opposite categories of elements of the point topology. The
strong monoidal pushforward
`PresheafOfModules.pushforward₀OfCommRingCat`
(`Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal`) moves
the sectionwise tensor to those categories, and the present statement then
applies.

Pinned Mathlib interfaces (commit `5ed2965256430c3649e86755f9576b54eca72435`)
that a proof may use:

- `Algebra/Category/ModuleCat/Presheaf/ColimitFunctor.lean`: for a colimit
  cocone `cR` of a ring presheaf on a cofiltered, locally and initially small
  category and a colimit cocone of `M.presheaf`, `PresheafOfModules.ModuleColimit`
  puts a `cR.pt`-module structure on the abelian-group colimit.
  `PresheafOfModules.colimitFunctor` and `PresheafOfModules.colimitAdjunction`
  (left adjoint to `PresheafOfModules.constFunctor`) make it functorial.
- `Algebra/Category/ModuleCat/Presheaf/Monoidal.lean`: the sectionwise tensor
  and its component lemma `PresheafOfModulesOfCommRing.tensorHom_app`.

Mathlib at this commit has no comparison isomorphism between the colimit of a
sectionwise tensor and the tensor of colimits.
`Algebra/Category/ModuleCat/Stalk.lean` defines module structures on stalks but
has no such tensor comparison either.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
