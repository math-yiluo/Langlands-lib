# Stalk support and finite closed support of scheme modules

Author: Worker 716.

This module defines the support of an actual `𝒪_X`-module on a scheme as its set of points with
nonzero stalk. It also defines a derived predicate, `HasFiniteClosedSupport`: the support is
finite and consists of closed points. A small proved interface follows. Everything lives in
the namespace `Langlands.AlgebraicGeometry.Modules`, for an arbitrary universe `u` and a
scheme `X : Scheme.{u}`. The module imports only Mathlib (`Mathlib.Algebra.Category.Grp.Zero`,
`Mathlib.AlgebraicGeometry.Modules.Sheaf`, `Mathlib.Topology.Sheaves.Abelian`).

## Definitions

### Stalk support

```lean
def stalkSupport (M : X.Modules) : Set X :=
  {x | ¬ IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj M.presheaf)}
```

Here `M : X.Modules` is an actual sheaf of modules over Mathlib's structure sheaf
`X.ringCatSheaf`. `M.presheaf : TopCat.Presheaf AddCommGrpCat X` is its underlying presheaf of
abelian groups. `TopCat.Presheaf.stalkFunctor AddCommGrpCat x` takes the stalk at `x`, the
colimit over the open neighbourhoods of `x`, computed in `AddCommGrpCat`. A point `x` belongs to
`stalkSupport M` exactly when this abelian group is not a zero object of `AddCommGrpCat`.

**Source.** This is the support of Stacks Project, Definition 17.5.1 (tag 01AT, label
`definition-support` in `modules.tex` at commit `a04446e57ec1fbc252a871afcec7752fb2807b14`,
label at line 470, definition environment at lines 469–482), in Section 17.5 "Supports of
modules and sections" (tag 01AS). The source file is in the registered folder
`stacks-closed-immersion-exactness-a04446e5`. Let `(X, 𝒪_X)` be a ringed space and `ℱ` a sheaf
of `𝒪_X`-modules. Then "the support of `ℱ` is the set of points `x ∈ X` such that
`ℱ_x ≠ 0`", written `Supp(ℱ)`. The Lean definition specializes this to the ringed space
underlying a scheme. It formalizes part (1) of the source definition only. The support of a
section, part (3), is not defined here.

**Role of the underlying abelian stalk.** Stacks reads the condition `ℱ_x ≠ 0` for the stalk
`ℱ_x` as an `𝒪_{X,x}`-module. The underlying abelian group of that module is the colimit of the
groups `ℱ(U)` over the open neighbourhoods `U` of `x`, which is the stalk of the underlying
abelian presheaf. A module is zero exactly when its underlying abelian group is zero. So
nonvanishing of the abelian stalk is the same condition as nonvanishing of the module stalk.
The Lean definition uses the abelian stalk directly and defines no `𝒪_{X,x}`-module stalk. The
paragraph above explains why this matches the source; it is not a formalized comparison.

### Finite closed support

```lean
def HasFiniteClosedSupport (M : X.Modules) : Prop :=
  (stalkSupport M).Finite ∧ ∀ x ∈ stalkSupport M, IsClosed ({x} : Set X)
```

This is a `Prop`. It holds when `stalkSupport M` is a finite set and every point of it is a
closed point of `X`, meaning the singleton `{x}` is closed in the topology of `X`. No other
condition is imposed: the predicate does not separately require the support to be closed, and
it puts no finiteness, coherence or noetherian hypothesis on `M` or `X`.

**Provenance.** This predicate is a derived convenience introduced for downstream
finite-support detection work. It is not a definition from the cited source. It combines the
Stacks support above with the usual notion of a closed point.

## Proved interface

All results below are proved, with no hypotheses beyond those displayed. Throughout,
`M N : X.Modules`.

- `mem_stalkSupport : x ∈ stalkSupport M ↔ ¬ IsZero ((TopCat.Presheaf.stalkFunctor
  AddCommGrpCat.{u} x).obj M.presheaf)` is the membership formula. It holds by definition
  (`Iff.rfl`).
- `mem_stalkSupport_iff_nontrivial : x ∈ stalkSupport M ↔ Nontrivial (M.presheaf.stalk x)`
  restates membership as the existence of a nonzero element in the abelian stalk.
  `TopCat.Presheaf.stalk M.presheaf x` is by definition the object computed by the stalk
  functor. The proof rewrites with Mathlib's `AddCommGrpCat.isZero_iff_subsingleton` and
  `not_subsingleton_iff_nontrivial`.
- `stalkSupport_eq_of_iso (e : M ≅ N) : stalkSupport M = stalkSupport N`: isomorphic
  modules have the same support. Proof: apply the functor `Scheme.Modules.toPresheaf X` and
  then the stalk functor at `x` to `e`. This gives an isomorphism of abelian stalks, and
  `Iso.isZero_iff` transfers being zero.
- `isZero_iff_forall_isZero_stalk : IsZero M ↔ ∀ x : X, IsZero ((TopCat.Presheaf.stalkFunctor
  AddCommGrpCat.{u} x).obj M.presheaf)`: a module is zero exactly when all its abelian stalks
  are zero. Proof: let `F := SheafOfModules.toSheaf X.ringCatSheaf`, the functor forgetting a
  module to its sheaf of abelian groups. It is faithful and preserves zero morphisms. So
  `IsZero M ↔ IsZero (F.obj M)`. One direction is `Functor.map_isZero`. For the other, if
  `F.obj M` is zero, then `F.map (𝟙 M) = 𝟙 (F.obj M) = 0`, and faithfulness gives `𝟙 M = 0`
  (`Functor.zero_of_map_zero`). Mathlib's `TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero`
  then says that the abelian sheaf `F.obj M` is zero exactly when all its stalks are zero. Its
  underlying presheaf is `M.presheaf` by definition.
- `stalkSupport_eq_empty_iff : stalkSupport M = ∅ ↔ IsZero M`: the support is empty exactly
  when the module is zero. This follows from the previous item.
- `hasFiniteClosedSupport_iff_exists_subset : HasFiniteClosedSupport M ↔ ∃ S : Set X,
  S.Finite ∧ (∀ x ∈ S, IsClosed ({x} : Set X)) ∧ stalkSupport M ⊆ S` is the finite-container
  formulation. Forward, take `S := stalkSupport M`. Backward, a subset of a finite set is
  finite, and each point of the support lies in `S` and so is closed.
- `HasFiniteClosedSupport.of_subset (hS : S.Finite) (hcl : ∀ x ∈ S, IsClosed ({x} : Set X))
  (hsub : stalkSupport M ⊆ S) : HasFiniteClosedSupport M`: containment of the support in a
  finite set of closed points gives finite closed support. This is the backward direction above.
- `hasFiniteClosedSupport_iff_of_iso (e : M ≅ N) : HasFiniteClosedSupport M ↔
  HasFiniteClosedSupport N`: finite closed support is invariant under isomorphism, by
  `stalkSupport_eq_of_iso`.
- `HasFiniteClosedSupport.of_isZero (h : IsZero M) : HasFiniteClosedSupport M`: a zero module
  has empty support, hence finite closed support.

The declarations use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope

This module supplies support vocabulary only. It makes no assertion about coherence,
quasi-coherence, support of higher direct images, flasqueness or cohomological vanishing. It
proves no closedness of supports in general. Stacks notes after Lemma 17.5.2 (tag 01AU,
`modules.tex` line 515) that the support of a sheaf of modules need not be closed.
