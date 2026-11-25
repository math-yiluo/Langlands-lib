/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Finite locally free and invertible sheaves of modules

A sheaf of modules is *finite locally free of rank `r`* if it admits local generators data
which is locally free data and whose generating families are each indexed by a type with
exactly `r` elements, and *invertible* if it is locally free of rank one, i.e. if those
generating families are indexed by one-element types.

The rank-one case of `SheafOfModules.IsFiniteLocallyFreeOfRank` and
`SheafOfModules.IsInvertible` say the same thing up to the difference between `Fin 1` and a
`Unique` index type (`SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one`).

## Main definitions

- `SheafOfModules.IsFiniteLocallyFreeOfRank`: `M : SheafOfModules R` is finite locally free of
  rank `r`.
- `SheafOfModules.IsFiniteLocallyFree`: `M : SheafOfModules R` is finite locally free, of a rank
  that may vary; `SheafOfModules.isFiniteLocallyFree` is the corresponding property of objects.
- `SheafOfModules.LocalGeneratorsData.IsInvertibleData`: a predicate on
  `q : M.LocalGeneratorsData` saying that `q` is locally free data whose generating families
  are each indexed by a type with exactly one element.
- `SheafOfModules.IsInvertible`: `M : SheafOfModules R` is invertible if there exists
  invertible data for it.

## Main results

- `SheafOfModules.IsInvertible.of_iso` and `SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso`:
  invertibility and finite local freeness of rank `r` only depend on the isomorphism class.
- `SheafOfModules.instIsInvertibleUnit`: the unit sheaf `𝒪` is invertible.
- `SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free`: a sheaf of modules which is
  locally free of finite rank on a covering is finite locally free.
- `SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one`: a sheaf of modules is
  invertible if and only if it is finite locally free of rank one.
-/

@[expose] public section

universe u v₁ u₁

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

noncomputable section

namespace SheafOfModules

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The free sheaf of modules on a one-element type is the unit sheaf of modules. -/
def freeUniqueIso (I : Type u) [Unique I] : free (R := R) I ≅ unit R :=
  coproductUniqueIso (fun _ : I ↦ unit R)

end

section

variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace LocalGeneratorsData

/-- Local generators data `q` is *invertible data* if it is locally free data whose
families of generators are each indexed by a type with exactly one element. -/
class IsInvertibleData {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) : Prop
    extends q.IsLocallyFreeData where
  nonempty_unique (i : q.I) : Nonempty (Unique (q.generators i).I)

/-- The transport of local generators data along an isomorphism of sheaves of modules. -/
@[simps]
def ofIso {M N : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) (e : M ≅ N) :
    N.LocalGeneratorsData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi (((overFunctor R (q.X i)).mapIso e).hom)

instance isLocallyFreeData_ofIso {M N : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsLocallyFreeData] (e : M ≅ N) : (q.ofIso e).IsLocallyFreeData where
  isIso i := by
    change IsIso ((q.generators i).ofEpi _).π
    rw [GeneratingSections.ofEpi_π]
    infer_instance

instance isInvertibleData_ofIso {M N : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsInvertibleData] (e : M ≅ N) : (q.ofIso e).IsInvertibleData where
  nonempty_unique i := IsInvertibleData.nonempty_unique (q := q) i

instance IsInvertibleData.shrink {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsInvertibleData] : q.shrink.IsInvertibleData where
  __ := (inferInstance : q.shrink.IsLocallyFreeData)
  nonempty_unique i := IsInvertibleData.nonempty_unique (q := q) i.2.choose

end LocalGeneratorsData

/-- A sheaf of modules is *invertible* if it is locally free of rank one, i.e. if there
exist local generators satisfying `IsInvertibleData`.

The isomorphism classes of invertible `𝒪_X`-modules on a scheme `X` form the Picard group
`AlgebraicGeometry.Scheme.Pic`.

(blueprint: `def-sc-invertible-module`) -/
class IsInvertible (M : SheafOfModules.{u} R) : Prop where
  exists_isInvertibleData : ∃ q : LocalGeneratorsData.{u₁} M, q.IsInvertibleData

theorem LocalGeneratorsData.isInvertible {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsInvertibleData] : M.IsInvertible := ⟨q.shrink, inferInstance⟩

instance (priority := 100) IsInvertible.isLocallyFree (M : SheafOfModules.{u} R)
    [h : M.IsInvertible] : M.IsLocallyFree :=
  have := h.exists_isInvertibleData.choose_spec
  ⟨h.exists_isInvertibleData.choose, inferInstance⟩

theorem IsInvertible.of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N) [h : M.IsInvertible] :
    N.IsInvertible := by
  obtain ⟨q, hq⟩ := h.exists_isInvertibleData
  exact (q.ofIso e).isInvertible

/-- A sheaf of modules is *finite locally free of rank `r`* if it admits local generators data
which is locally free data (`SheafOfModules.LocalGeneratorsData.IsLocallyFreeData`) and whose
family of generators over each member of the covering is indexed by a type with exactly `r`
elements. Such a sheaf of modules is in particular locally free, hence quasi-coherent. -/
@[stacks 01C6]
class IsFiniteLocallyFreeOfRank (M : SheafOfModules.{u} R) (r : ℕ) : Prop where
  exists_localGeneratorsData : ∃ q : LocalGeneratorsData.{u₁} M, ∃ _ : q.IsLocallyFreeData,
    ∀ i, Nonempty ((q.generators i).I ≃ Fin r)

/-- A finite locally free sheaf of modules is locally free.

This cannot be an instance: the rank `r` does not occur in the goal `M.IsLocallyFree`, so
type-class synthesis has no way to determine it. -/
theorem IsFiniteLocallyFreeOfRank.isLocallyFree (M : SheafOfModules.{u} R)
    (r : ℕ) [h : M.IsFiniteLocallyFreeOfRank r] : M.IsLocallyFree :=
  have := h.exists_localGeneratorsData.choose_spec.choose
  ⟨_, this⟩

theorem IsFiniteLocallyFreeOfRank.of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N) {r : ℕ}
    [h : M.IsFiniteLocallyFreeOfRank r] : N.IsFiniteLocallyFreeOfRank r := by
  obtain ⟨q, hq, hr⟩ := h.exists_localGeneratorsData
  exact ⟨q.ofIso e, inferInstance, hr⟩

/-- A sheaf of modules is *finite locally free* if it admits local generators data which is
locally free data (`SheafOfModules.LocalGeneratorsData.IsLocallyFreeData`) with finitely many
generators over each member of the covering. Unlike `SheafOfModules.IsFiniteLocallyFreeOfRank`,
the rank may vary from one member of the covering to another. -/
@[stacks 01C6]
class IsFiniteLocallyFree (M : SheafOfModules.{u} R) : Prop where
  exists_localGeneratorsData :
    ∃ q : LocalGeneratorsData.{u₁} M, q.IsLocallyFreeData ∧ q.IsFiniteType

/-- A finite locally free sheaf of modules is locally free, hence quasi-coherent. -/
instance (priority := 100) IsFiniteLocallyFree.isLocallyFree (M : SheafOfModules.{u} R)
    [h : M.IsFiniteLocallyFree] : M.IsLocallyFree :=
  have := h.exists_localGeneratorsData.choose_spec.1
  h.exists_localGeneratorsData.choose.isLocallyFree

variable (R) in
/-- The finite locally free sheaves of modules, as a property of objects. -/
abbrev isFiniteLocallyFree : ObjectProperty (SheafOfModules.{u} R) :=
  fun M ↦ M.IsFiniteLocallyFree

theorem IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (M : SheafOfModules.{u} R) (r : ℕ)
    [h : M.IsFiniteLocallyFreeOfRank r] : M.IsFiniteLocallyFree := by
  obtain ⟨q, hq, hr⟩ := h.exists_localGeneratorsData
  exact ⟨q, hq, ⟨fun i ↦ ⟨Finite.of_equiv _ (hr i).some.symm⟩⟩⟩

theorem IsFiniteLocallyFree.of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N)
    [h : M.IsFiniteLocallyFree] : N.IsFiniteLocallyFree := by
  obtain ⟨q, hq, hf⟩ := h.exists_localGeneratorsData
  refine ⟨q.ofIso e, inferInstance, ⟨fun i ↦ ?_⟩⟩
  have := hf.isFiniteType i
  exact inferInstanceAs ((q.generators i).ofEpi _).IsFiniteType

instance (priority := 100) IsInvertible.isFiniteLocallyFree (M : SheafOfModules.{u} R)
    [h : M.IsInvertible] : M.IsFiniteLocallyFree := by
  obtain ⟨q, hq⟩ := h.exists_isInvertibleData
  refine ⟨q, inferInstance, ⟨fun i ↦ ⟨?_⟩⟩⟩
  have := (hq.nonempty_unique i).some
  infer_instance

/-- A sheaf of modules is invertible if and only if it is finite locally free of rank one. -/
theorem isInvertible_iff_isFiniteLocallyFreeOfRank_one (M : SheafOfModules.{u} R) :
    M.IsInvertible ↔ M.IsFiniteLocallyFreeOfRank 1 := by
  refine ⟨fun ⟨q, hq⟩ ↦ ⟨q, inferInstance, fun i ↦ ?_⟩, fun ⟨q, hq, hr⟩ ↦ ⟨q, ?_⟩⟩
  · have := (hq.nonempty_unique i).some
    exact ⟨Equiv.ofUnique _ _⟩
  · exact { toIsLocallyFreeData := hq, nonempty_unique i := ⟨(hr i).some.unique⟩ }

end

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}] [HasBinaryProducts C]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

instance (I : Type u) [Unique I] :
    (free.generatingSections (R := R) I).localGeneratorsData.IsInvertibleData where
  nonempty_unique _ := ⟨inferInstanceAs (Unique I)⟩

instance (I : Type u) [Unique I] : (free (R := R) I).IsInvertible :=
  (free.generatingSections I).localGeneratorsData.isInvertible

instance : (unit R).IsInvertible :=
  IsInvertible.of_iso (freeUniqueIso (R := R) PUnit.{u + 1})

end

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sheaf of modules isomorphic to the unit is generated by a single section. -/
def generatingSectionsOfUnitIso {M : SheafOfModules.{u} R} (e : M ≅ unit R) :
    M.GeneratingSections :=
  (free.generatingSections PUnit.{u + 1}).ofEpi (freeUniqueIso _ ≪≫ e.symm).hom

instance {M : SheafOfModules.{u} R} (e : M ≅ unit R) :
    Unique (generatingSectionsOfUnitIso e).I :=
  inferInstanceAs (Unique PUnit.{u + 1})

instance {M : SheafOfModules.{u} R} (e : M ≅ unit R) :
    IsIso (generatingSectionsOfUnitIso e).π := by
  rw [generatingSectionsOfUnitIso, GeneratingSections.ofEpi_π]
  infer_instance

end

section

variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Local generators data for a sheaf of modules which is locally isomorphic to the unit:
over each `X i`, the single section corresponding to `1`. -/
@[simps]
def localGeneratorsDataOfUnitIso {M : SheafOfModules.{u} R} {I : Type u₁}
    (X : I → C) (hX : J.CoversTop X)
    (h : ∀ i, Nonempty (M.over (X i) ≅ unit (R.over (X i)))) : M.LocalGeneratorsData where
  I := I
  X := X
  coversTop := hX
  generators i := generatingSectionsOfUnitIso (h i).some

instance isInvertibleData_localGeneratorsDataOfUnitIso {M : SheafOfModules.{u} R} {I : Type u₁}
    (X : I → C) (hX : J.CoversTop X)
    (h : ∀ i, Nonempty (M.over (X i) ≅ unit (R.over (X i)))) :
    (localGeneratorsDataOfUnitIso X hX h).IsInvertibleData where
  isIso i := by rw [localGeneratorsDataOfUnitIso_generators]; infer_instance
  nonempty_unique i := by
    rw [localGeneratorsDataOfUnitIso_generators]
    exact ⟨inferInstance⟩

/-- A sheaf of modules which is locally isomorphic to the unit is invertible. -/
theorem isInvertible_of_forall_over_unit {M : SheafOfModules.{u} R} {I : Type u₁}
    (X : I → C) (hX : J.CoversTop X)
    (h : ∀ i, Nonempty (M.over (X i) ≅ unit (R.over (X i)))) : M.IsInvertible :=
  (localGeneratorsDataOfUnitIso X hX h).isInvertible

/-- A sheaf of modules is finite locally free of rank `r` if and only if it is isomorphic to the
free module of rank `r` over each object of a family covering the terminal object. -/
theorem isFiniteLocallyFreeOfRank_iff_exists_over_iso_free {M : SheafOfModules.{u} R} {r : ℕ} :
    M.IsFiniteLocallyFreeOfRank r ↔ ∃ (I : Type u₁) (X : I → C), J.CoversTop X ∧
      ∀ i, Nonempty (M.over (X i) ≅ free (ULift.{u} (Fin r))) := by
  constructor
  · rintro ⟨q, hq, hr⟩
    refine ⟨q.I, q.X, q.coversTop, fun i ↦ ⟨?_⟩⟩
    exact (asIso (q.generators i).π).symm ≪≫ freeFunctor.mapIso
      ((hr i).some.trans Equiv.ulift.symm).toIso
  · rintro ⟨I, X, hX, h⟩
    let q : M.LocalGeneratorsData :=
      { I := I
        X := X
        coversTop := hX
        generators i := (free.generatingSections _).ofEpi (h i).some.inv }
    have : q.IsLocallyFreeData := ⟨fun i ↦ by
      dsimp [q]
      rw [GeneratingSections.ofEpi_π]
      infer_instance⟩
    exact ⟨q, this, fun i ↦ ⟨Equiv.ulift⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- A sheaf of modules which is isomorphic to a free module on a finite type over each object of
a family covering the terminal object is finite locally free. -/
theorem isFiniteLocallyFree_of_exists_over_iso_free {M : SheafOfModules.{u} R} {I : Type u₁}
    (X : I → C) (hX : J.CoversTop X) (κ : I → Type u) [∀ i, Finite (κ i)]
    (h : ∀ i, Nonempty (M.over (X i) ≅ free (κ i))) : M.IsFiniteLocallyFree := by
  let q : M.LocalGeneratorsData :=
    { I := I
      X := X
      coversTop := hX
      generators i := (free.generatingSections _).ofEpi (h i).some.inv }
  have : q.IsLocallyFreeData := ⟨fun i ↦ by
    dsimp [q]
    rw [GeneratingSections.ofEpi_π]
    infer_instance⟩
  exact ⟨q, this, ⟨fun i ↦ ⟨inferInstanceAs (Finite (κ i))⟩⟩⟩

end

section

variable [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A finite locally free sheaf of modules is of finite presentation: locally it is free on
finitely many generators, with no relations. -/
instance (priority := 100) IsFiniteLocallyFree.isFinitePresentation (M : SheafOfModules.{u} R)
    [h : M.IsFiniteLocallyFree] : M.IsFinitePresentation := by
  obtain ⟨q, hq, hf⟩ := h.exists_localGeneratorsData
  refine ⟨q.quasiCoherentData, ⟨fun i ↦ ?_⟩⟩
  have := hf.isFiniteType i
  exact { isFiniteType_generators := this
          isFiniteType_relations := ⟨inferInstanceAs (Finite (ULift Empty))⟩ }

end

end SheafOfModules

end
