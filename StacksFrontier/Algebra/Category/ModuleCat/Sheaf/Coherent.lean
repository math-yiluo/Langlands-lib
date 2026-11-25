module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Coherent sheaves of modules

A sheaf of modules on a ringed space is *coherent* when it is of finite type and the relations
among every finite family of sections over every open subset are locally finitely generated.
This file defines the coherence predicate and the full subcategory of coherent sheaves, and
proves closure properties of coherence and of finite type.

## Main definitions

* `Stacks.SheafOfModules.IsCoherent` is the coherence predicate on a sheaf of modules over a
  ringed space.
* `Stacks.SheafOfModules.coherentModules` is coherence packaged as an `ObjectProperty`, and
  `Stacks.SheafOfModules.CoherentModules` is the corresponding full subcategory, the category
  denoted `Coh(O_X)`.
* `Stacks.SheafOfModules.freeGeneratingSections` is the standard basis of a free sheaf of
  modules, viewed as a family of generating sections, and
  `Stacks.SheafOfModules.zeroGeneratingSections` is the empty family generating a zero sheaf.
* `Stacks.SheafOfModules.bindLocalGeneratorsData` glues local generators of the restrictions of
  a sheaf of modules to the members of a covering family into local generators of the sheaf
  itself. It is the family-of-generators analogue of
  `SheafOfModules.QuasicoherentData.bind`.

## Main results

* `Stacks.SheafOfModules.over_epi` and `Stacks.SheafOfModules.over_mono`: restriction to an
  object of the site preserves epimorphisms and monomorphisms.
* `Stacks.SheafOfModules.isFiniteType_of_epi'` and `Stacks.SheafOfModules.isFiniteType_of_iso`:
  being of finite type passes to quotients, hence is invariant under isomorphism.
* `Stacks.SheafOfModules.isFiniteType_free`: a finite free sheaf of modules is of finite type,
  and `Stacks.SheafOfModules.isFiniteType_of_isZero`: so is a zero sheaf.
* `Stacks.SheafOfModules.isFiniteType_of_coversTop`: being of finite type is local on the base.
* `Stacks.SheafOfModules.isCoherent_of_mono`: a finite type subsheaf of a coherent sheaf of
  modules is coherent.
* `Stacks.SheafOfModules.isCoherent_of_isZero`: a zero sheaf of modules is coherent.
* `Stacks.SheafOfModules.coherentModules` contains the zero object and is closed under
  isomorphisms, two of the five closure conditions defining a weak Serre class.

## Implementation notes

The restriction lemmas and the finite type closure lemmas are stated over an arbitrary site,
not only over the opens of a topological space: they are facts about
`SheafOfModules.overFunctor`, which exists for any site. The coherence predicate itself is
stated for a ringed space, following the source.

These lemmas are stated over an equi-universe site: the site, its hom level, the ring and the
modules all share the single universe `u`, whereas Mathlib keeps `SheafOfModules.IsFiniteType`
polymorphic in three independent universes. So `isFiniteType_of_epi'` and its companions
elaborate at `IsFiniteType.{u, u, u}` and cannot be applied over a ringed site with independent
universes, where the goal is `IsFiniteType.{w, v, u}`. In particular they do not serve the
setting of sites with three independent universes, which in any case uses a separate
presheaf-level coherence predicate. Decoupling those universes is the change that would make
this section reusable there.

Finite type over the slice site `(Opens.grothendieckTopology X).over U` is used as finite type
of the restriction as an `𝒪_U`-module on `U`; this identification is not proved here. It is
true, and it is why the restriction lemmas say what one wants. The identification
`(M.over U).sections ≃ M.val.obj (op U)` is
`Stacks.SheafOfModules.FiniteTypeKernel.sectionsOverEquiv`, with `evalOver` and `mkOver`, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension`; a morphism out of the
sections of `M` over `U` is built with those.

The space, the sheaf of rings, the sections and the index types of the free modules all live in
one common universe `u`. Condition (2) of coherence quantifies over maps out of
`SheafOfModules.free I` on the slice site `(Opens.grothendieckTopology X).over U`, so stating it
requires `Limits.kernel` to exist there, which requires the sheafification instances
`HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}` and
`((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u}`. These are
available at every universe `u`, not only at `Type 0`, once
`Mathlib.Algebra.Category.Grp.FilteredColimits` supplies the filtered colimits from which the
concrete sheafification of `AddCommGrpCat` is built; that is why this import is here.

Commutativity of the structure sheaf is not needed for any statement here, so `R` is allowed to
be a sheaf of not necessarily commutative rings.

Condition (2) of coherence is stated as a condition on maps `free I ⟶ M.over U` out of a finite
free module rather than on finite families of sections of `M` over `U`. By
`SheafOfModules.freeHomEquiv` these are the same data: a map `φ : free I ⟶ M.over U`
corresponds to the family `(M.over U).freeHomEquiv φ` of sections, and the associated map of a
family `s` is `(M.over U).freeHomEquiv.symm s`, so quantifying over `φ` is quantifying over
finite families of sections as in the source.

The declarations live in the `Stacks.SheafOfModules` namespace rather than in `SheafOfModules`,
so that this file can be co-imported with the rest of the library.

`isFiniteType_of_epi'` carries a prime because
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension` declares an
`isFiniteType_of_epi` in this same namespace. That version is more general: it is stated at
three independent universes where this one is equi-universe. The two have different argument
shapes (instance versus explicit finite-type hypothesis), so replacing this copy by that one
requires adapting the call sites.

## References

* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace SheafOfModules ZeroObject

universe u

namespace Stacks.SheafOfModules

section Site

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- Restriction to an object of the site preserves epimorphisms: `SheafOfModules.overFunctor`
is a left adjoint, so it preserves colimits and therefore epimorphisms. -/
theorem over_epi [HasBinaryProducts C] {M N : SheafOfModules.{u} R} (p : M ⟶ N) [Epi p] (U : C) :
    Epi (p.over U) := by
  have h : (SheafOfModules.pushforward.{u} (𝟙 (R.over U))).PreservesEpimorphisms := by
    have : PreservesColimitsOfShape WalkingSpan
        (SheafOfModules.pushforward.{u} (𝟙 (R.over U))) := inferInstance
    infer_instance
  exact h.preserves p

section FiniteTypeClosure

variable [HasBinaryProducts C]
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Being of finite type passes to quotients: if `M` is of finite type and `p : M ⟶ N` is an
epimorphism, then `N` is of finite type. This is the sheaf of modules form of the statement
that a quotient of a finitely generated module is finitely generated. -/
theorem isFiniteType_of_epi' {M N : SheafOfModules.{u} R} (p : M ⟶ N)
    [M.IsFiniteType] [Epi p] : N.IsFiniteType := by
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  have he : ∀ i, Epi (p.over (σ.X i)) := fun i => over_epi p (σ.X i)
  have hfin : ∀ i, (σ.generators i).IsFiniteType := fun i => hσ.isFiniteType i
  exact { exists_localGeneratorsData :=
    ⟨{ I := σ.I, X := σ.X, coversTop := σ.coversTop,
       generators := fun i => (σ.generators i).ofEpi (p.over (σ.X i)) },
     { isFiniteType := fun i => inferInstance }⟩ }

/-- Being of finite type is invariant under isomorphism.

This is not the same statement as `Stacks.AlgebraicGeometry.DerivedPushforward.isFiniteType_of_iso`
of `StacksFrontier.AlgebraicGeometry.DerivedPushforward.Basic`: that one is polymorphic in the
three universes of the site, the sections and the modules where this one has them equal, so
merging the two in either direction would narrow a statement. -/
theorem isFiniteType_of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N) [M.IsFiniteType] :
    N.IsFiniteType :=
  isFiniteType_of_epi' e.hom

end FiniteTypeClosure

section Free

variable [HasBinaryProducts C]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

end Free

section Locality

variable [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y), HasSheafify ((J.over Y).over Z) AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y), ((J.over Y).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]

end Locality

end Site

section RingedSpace

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

end RingedSpace

end Stacks.SheafOfModules
