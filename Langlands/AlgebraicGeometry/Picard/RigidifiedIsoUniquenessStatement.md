# Uniqueness of actual rigidified abelian-scheme isomorphisms

`Langlands.AbelianScheme.RigidifiedIsoUniquenessStatement.{u}` states that
between two actual rigidified line bundles on `T ×_S A` there is at most one
rigidified isomorphism. This holds for every abelian scheme `A` over every
base `S` and for every test scheme `T` over `S`. The statement does not assert
that an isomorphism exists. This file defines the proposition only. It
supplies no proof.

## Exact interface

The statement quantifies over every `S : Scheme.{u}`, every
`A : AbelianScheme S`, every `T : Over S` and every pair
`L M : RigidifiedFamily A T`. Its conclusion is `Subsingleton (L ≅ M)`, so any
two elements of the type of isomorphisms from `L` to `M` are equal. There are
no further hypotheses.

`RigidifiedFamily A T` is the published abbreviation from
`Langlands.AlgebraicGeometry.Picard.RelativePicardZero`. It is the relative
rigidified line-bundle category
`RigidifiedLineBundle.relative A.X.hom (unitSection A) (unitSection_comp A) T`,
for the following data:

- The total space is `(relativeSpace A.X.hom).obj T`, the chosen pullback of
  `T.hom` and `A.X.hom`. This is `T ×_S A`, with `T` as the first factor.
- `unitSection A : S ⟶ A.X.left` is the identity point of the group-valued
  functor of points of `A`. `unitSection_comp A` records that it is a section
  of `A.X.hom`.
- The rigidifying section is
  `ε_T = (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T`.
  This is the morphism `T.left ⟶ T ×_S A` with components `𝟙 T.left` and
  `T.hom ≫ unitSection A`.

An object of the category is a sheaf of modules `L.obj.carrier` on `T ×_S A`
together with an isomorphism

```lean
L.obj.rigidification :
  structureModule T.left ≅ (Scheme.Modules.pullback ε_T).obj L.obj.carrier
```

and a proof that the carrier is `IsLocallyFreeRankOne`. That property says
that every point has an open neighbourhood on which the restricted module is
isomorphic to the unit sheaf of modules. The category is the full subcategory
of `Langlands.SchemeModule.RigidifiedModule ε_T` on such objects. A morphism
`L ⟶ M` is therefore an actual morphism `f` of module sheaves satisfying

```lean
L.obj.rigidification.hom ≫ (Scheme.Modules.pullback ε_T).map f =
  M.obj.rigidification.hom
```

in diagrammatic composition order. `L ≅ M` is Mathlib's `CategoryTheory.Iso`
in this category. Such an isomorphism consists of rigidified morphisms in both
directions whose two composites are identities. `RigidifiedLineBundle.isoMk`
builds one from a module isomorphism satisfying the displayed compatibility.

No restriction is placed on `S` or `T`. In particular, nonreduced,
non-noetherian and non-quasi-separated tests are included. The bundles `L` and
`M` need not satisfy the geometric Picard-zero condition. The statement adds
no hypothesis on global functions, no classification of automorphisms by
scalars, and no triviality hypothesis on rigidified automorphisms.

### Equivalent formulations

These equivalences explain the proposition. They are not formalized in this
file.

An isomorphism is determined by its forward morphism (`Iso.ext`). A morphism
of `RigidifiedFamily A T` is determined by its underlying module morphism,
because the rigidification condition is a property of that morphism. Hence
the proposition says that two rigidified isomorphisms `L ≅ M` have the same
underlying module isomorphism.

For fixed `S`, `A` and `T`, uniqueness for all pairs `L`, `M` is equivalent to
triviality of rigidified automorphisms. Taking `M = L` shows that every
`e : L ≅ L` equals `Iso.refl L`. Conversely, let `e e' : L ≅ M`, and suppose
every automorphism of `L` is the identity. Then `e ≪≫ e'.symm` is the
identity of `L`. Composing with `e'` gives `e.hom = e'.hom`, and so `e = e'`.
The proposition is stated in the uniqueness form because its consumer
compares two given isomorphisms. The automorphism form is the source's
wording.

The proposition concerns isomorphisms only. It does not state that every
rigidified endomorphism of `L` is the identity, which is the stronger
conclusion available in the source argument below.

## Derived provenance

This is a derived statement, internal to the project's separatedness route.
It specializes a deduction in Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft, Chapter VI §1, paragraph (6.2), printed p.88
(PDF p.92). The source is registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Printed pp.88–89 (PDF pp.92–93) were read. No source-specific errata for this
draft were found in the project literature collection or published notes.

Under its hypotheses `(∗)`, the source assumes that `f : X → S` is
quasi-compact and quasi-separated, that `f_*(O_(X ×_S T)) = O_T` for all
`S`-schemes `T`, and that `f` has a section `ε`. A rigidification of a line
bundle `L` on `X_T` along the induced section `ε_T : T → X_T` is an
isomorphism `α : O_T ≅ ε_T^* L`. A homomorphism `h : (L₁, α₁) → (L₂, α₂)` is a
homomorphism of line bundles with `(ε^* h) ∘ α₁ = α₂`. The source then says
that an endomorphism of `(L, α)` is given by some `h ∈ Γ(X_T, O_(X_T))` with
`ε^*(h) = 1`. Using `f_*(O_(X_T)) = O_T`, it concludes that "rigidified line
bundles on `X_T` have no nontrivial automorphisms". Next on the same page it
defines the functor `P_{X/S,ε}` of rigidified isomorphism classes.

The Library objects correspond to the source's as follows.

- `X → S` is the structure morphism `A.X.hom`, and `ε` is `unitSection A`.
- The source writes `X_T = X ×_S T`. The Library's total space is
  `T ×_S A`, by the convention of the published relative family. The
  explicit symmetry `relativeSpaceSymmetry` relates the two orders elsewhere.
- The source's `ε_T` is the Library's `ε_T` above.
- A line bundle is an `IsLocallyFreeRankOne` module sheaf, and `α` is
  `rigidification`, with the same direction `O_T ≅ ε_T^* L`.
- The source's condition `(ε^* h) ∘ α₁ = α₂` is the displayed Library condition
  `α₁.hom ≫ ε_T^* h = α₂.hom`, written in diagrammatic order.

The specialization to abelian schemes removes the source's hypotheses from the
statement. `unitSection A` supplies the section. The global-functions
hypothesis is omitted because a published theorem supplies it for abelian
schemes, not because it is assumed silently.
`Langlands.AbelianScheme.universalGlobalFunctions` proves that for every
`T : Over S` the actual projection `T ×_S A → T` induces an isomorphism on
global functions. It follows from
`Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions`, since that
projection is a base change of the smooth, proper and geometrically connected
morphism `A.X.hom`. This is the global-sections form of the source's
condition. The source's deduction uses only the global functions
`Γ(X_T, O_(X_T)) = Γ(T, f_*O_(X_T))`. That deduction does not cite the
quasi-compactness and quasi-separatedness hypothesis. The hypothesis holds
anyway for the proper morphism `A.X.hom`, but this statement does not use it.
Using the published theorem is an obligation of the proof, not part of this
statement.

The proposition is therefore not an unconditional theorem in the source's
wording. The source states triviality of automorphisms for a general
morphism `f` satisfying `(∗)`. This statement fixes `f` to the structure
morphism of an abelian scheme and has no hypotheses. It replaces the
automorphism wording by the equivalent uniqueness of isomorphisms. It also
uses the actual Library categories of module sheaves, pullback functors and
rigidified line bundles.

The proposition isolates the automorphism-rigidity input of the published
`Langlands.AbelianScheme.RigidifiedClassesZariskiSeparatedStatement`, in
module `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedStatement`.
One route in that file's remaining proof obligations uses exactly this
uniqueness. Local rigidified isomorphisms between pulled-back representatives
must agree on the pulled-back overlaps before they can be glued. This file
asserts no gluing, separatedness or sheaf property. It also states no
ordinary Picard functor and no ordinary/rigidified comparison.

The Lean interface was designed by Worker 453.

## Remaining proof obligations

A proof must establish the exact proposition for every `S`, `A`, `T`, `L` and
`M`, without new hypotheses. One route has the following steps.

1. Show that every automorphism of an `IsLocallyFreeRankOne` module sheaf `L`
   on a scheme `X` is multiplication by a unique global unit of `Γ(X, ⊤)`.
   The source uses this step without proof. It is not yet in the Library.
   `Langlands.SchemeModule.structureAutMulEquiv` in
   `Modules.StructureUnitScalars` classifies automorphisms only of the
   structure module. The scalar action `Langlands.Scheme.Modules.scalarHom` in
   `ModuleLinear` multiplies morphisms of arbitrary module sheaves by global
   functions, but does not classify their automorphisms. The local scalars
   obtained from trivializations must be shown to be independent of the
   trivialization and to glue to a global unit.
2. Show that the rigidification condition forces the image of this unit under
   `ε_T` on global functions to be `1` in `Γ(T.left, ⊤)`. This identifies the
   pulled-back scalar automorphism, through `L.obj.rigidification`, with an
   automorphism of `structureModule T.left`.
3. Use `universalGlobalFunctions` with the published relative unit descent in
   `Langlands.AbelianScheme.RelativeGlobalUnits`, for example
   `relativeUnitDescend_eq_section` and `relativeUnitsPullback_injective`.
   These identify a global unit on `T ×_S A` with the pullback, along the
   projection to `T`, of its image under `ε_T`. Hence the unit is `1`, and the
   automorphism is the identity.
4. Deduce uniqueness of isomorphisms by the groupoid argument above and
   `Iso.ext`.

These are obligations of a separate exact-target proof task. The ordinary
Picard and fppf, ordinary/rigidified comparison, relative existence, relative
geometry, field existence and openness, and global-functions workflows retain
their separate ownership and existing controls.
