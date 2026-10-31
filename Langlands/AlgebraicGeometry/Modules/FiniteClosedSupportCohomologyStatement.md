# Cohomology and zero detection for scheme modules with finite closed support

Authors: Worker 360 and Worker 716.

This file defines a proposition and does not prove it.
`Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportCohomologyStatement.{u}`
is a Prop-valued definition for an arbitrary universe `u`. It is a target for a
separate later proof. The module imports
`Langlands.AlgebraicGeometry.Modules.ModuleSupport` and
`Langlands.AlgebraicGeometry.Modules.DerivedSections` unchanged and defines
nothing else.

## The proposition

```lean
def FiniteClosedSupportCohomologyStatement : Prop :=
  ∀ (X : Scheme.{u}) (M : X.Modules),
    HasFiniteClosedSupport M →
    (∀ n : ℕ, IsZero ((DerivedSections.cohomology X (n + 1)).obj M)) ∧
    (IsZero ((DerivedSections.globalSections X).obj M) ↔ IsZero M) ∧
    ∀ (R : CommRingCat.{u}) (f : X ⟶ Spec R),
      (∀ n : ℕ, IsZero ((DerivedSections.relativeCohomology f (n + 1)).obj M)) ∧
      (IsZero ((DerivedSections.relativeGlobalSections f).obj M) ↔ IsZero M)
```

In words: for every scheme `X : Scheme.{u}` and every actual sheaf of modules
`M : X.Modules` over Mathlib's structure sheaf `X.ringCatSheaf` with finite closed
support,

1. `Hⁿ⁺¹(X, M)` is a zero object for every `n : ℕ`, that is, in every positive degree;
2. the global-section module `Γ(X, M)` is a zero object exactly when `M` is a zero
   object of `X.Modules`;
3. for every commutative ring `R : CommRingCat.{u}` and every morphism of schemes
   `f : X ⟶ Spec R`, the same two assertions hold for the `R`-module versions:
   `Hⁿ⁺¹(X, M)` as an `R`-module vanishes for every `n : ℕ`, and the `R`-module of
   global sections is zero exactly when `M` is zero.

`IsZero` is Mathlib's zero-object predicate. In `ModuleCat` it means the module is
trivial. In `X.Modules` it means that `M` is a zero object of the abelian category of
sheaves of `𝒪_X`-modules.

## The functors

All functors come from `Langlands.AlgebraicGeometry.Modules.DerivedSections`. They act on
actual structure-sheaf modules; none is cohomology of a constant sheaf or of an abstract
topological space.

- `DerivedSections.globalSections X : X.Modules ⥤ ModuleCat Γ(X, ⊤)` is
  `SheafOfModules.evaluation X.ringCatSheaf (op ⊤)`: sections over the top open, as a
  module over the global functions `Γ(X, ⊤)`.
- `DerivedSections.cohomology X n` is `(globalSections X).rightDerived n`, Mathlib's
  `n`-th right derived functor. It is computed from Mathlib's chosen injective
  resolutions in `X.Modules`, which is a Grothendieck abelian category and so has
  enough injectives.
- `DerivedSections.relativeGlobalSections f : X.Modules ⥤ ModuleCat R` is the composite
  `Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor`: push `M` forward to `Spec R`
  and take global sections there as an `R`-module.
- `DerivedSections.relativeCohomology f n` is
  `(relativeGlobalSections f).rightDerived n`.

The two zero-detection equivalences concern these global-section objects. Through the
published isomorphisms `DerivedSections.cohomologyZeroIso` and
`DerivedSections.relativeCohomologyZeroIso`, which identify degree-zero cohomology with
global sections, they are equivalent to the corresponding detection by degree-zero
cohomology. The proposition does not state that degree-zero formulation separately.

## Support convention

`HasFiniteClosedSupport M` is the published predicate of
`Langlands.AlgebraicGeometry.Modules.ModuleSupport`. It says that `stalkSupport M` is a
finite set and that each of its points is closed, meaning `{x}` is a closed subset of
`X`. Here `stalkSupport M` is the set of points at which the stalk of the underlying
abelian presheaf `M.presheaf` is not a zero object. This is the support of Stacks
Project Definition 17.5.1 (tag 01AT); see `ModuleSupport.md` for the source locator
and the comparison between abelian and module stalks.

The hypothesis concerns the support itself, not its closure. The predicate does not
require the support to be closed as a set, although a finite set of closed points is
closed.

## Scope

The only premise on `M` is `HasFiniteClosedSupport M`. There is no coherence,
quasi-coherence, finite-generation, noetherian, separatedness, properness, smoothness
or flatness hypothesis on `X`, `M`, `R` or `f`. The morphism `f` is arbitrary. The
quantifiers include the empty scheme, modules with empty support (the zero modules),
every positive degree `n + 1`, and an arbitrary universe `u` shared by `X`, `M` and `R`.

The proposition asserts vanishing only in positive degrees. It does not assert that
finite-support modules have zero global sections, or that they are zero; a skyscraper
module at a closed point with nonzero stalk has nonzero global sections. It asserts
nothing about higher direct images along morphisms other than through the affine base
`Spec R`, and nothing about Leray spectral sequences or base change.

## Provenance

The proposition is derived, internal content. It is not quoted from an external
source. The support convention is the cited Stacks definition above. The following
mathematical argument motivates the statement. It is a provenance rationale, not an
implemented Lean proof.

1. **Flasqueness of the underlying abelian sheaf.** Forget `M` to its abelian sheaf
   `(SheafOfModules.toSheaf X.ringCatSheaf).obj M`, whose underlying presheaf is
   `M.presheaf`. Let `S = stalkSupport M` and let `U` be open. Then `S ∩ U` is a finite
   union of closed singletons, hence closed in `X`. The opens `U` and
   `V = X \ (S ∩ U)` cover `X`. Every point of `U ∩ V` lies outside `S`, so every stalk
   on `U ∩ V` is zero and a section `s` over `U` restricts to zero there. Gluing `s`
   with the zero section over `V` gives a global section restricting to `s`. Hence every
   restriction map from `X` is surjective, and so is every restriction map between
   opens. The abelian sheaf is flasque.
2. **Zero detection by global sections.** If the global-section group is zero, the
   surjections from step 1 make every section group zero. So the abelian sheaf is a zero
   object. The forgetful functor `SheafOfModules.toSheaf X.ringCatSheaf` is faithful and
   preserves zero morphisms, so it reflects zero objects, and `M` is zero. Conversely, an
   additive functor sends a zero module to a zero object. The global-section module and
   the global-section group have the same underlying set, so either is zero exactly when
   the other is.
3. **Positive-degree vanishing.** The published theorem
   `Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclic.isZero_cohomology_succ_of_isFlasque`
   (module `Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof`)
   says that an `X.Modules` object whose underlying abelian presheaf is flasque has
   `IsZero ((DerivedSections.cohomology X (n + 1)).obj M)` for every `n`. Step 1
   supplies that flasqueness.
4. **Scalar restriction for the affine version.**
   `DerivedSections.relativeCohomologyRestrictScalarsIso f n` identifies
   `relativeCohomology f n` with `cohomology X n` followed by restriction of scalars
   along `DerivedSections.structureRingHom f : R ⟶ Γ(X, ⊤)`, the ring map
   `R → Γ(X, ⊤)` induced by `f`. Likewise `DerivedSections.relativeGlobalSectionsIso f`
   identifies `relativeGlobalSections f` with `globalSections X` followed by the same
   restriction of scalars, componentwise by identities. Restriction of scalars keeps
   the underlying abelian group. It therefore preserves and reflects zero objects, so
   steps 2 and 3 transfer to the affine base.

## Separate obligations

The published statement `Langlands.Cohomology.FiniteClosedSupportSheafStatement`
formulates steps 1 and 2 for arbitrary abelian sheaves on a topological space, with the
support contained in a finite set of closed points. That statement and its eventual proof
are independent obligations owned by a separate task. This file neither proves it nor
assumes it. A later proof of the present proposition can apply a proof of that sheaf
statement to the abelian sheaf underlying `M` with `S = stalkSupport M`, then use steps 3
and 4. That module proof is also a separate obligation, not supplied here.

Downstream finite-support cohomology detection for the projections of the square of an
abelian scheme plans to use this proposition as its acyclicity and zero-detection input.
The file proves no finite-support property of higher direct images, and no coherence,
Leray comparison or geometric base change.
